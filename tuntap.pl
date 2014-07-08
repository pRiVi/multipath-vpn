#!/usr/bin/perl -w
use strict;
use IO::File;
use POE;
use POE::Wheel::UDP;
use Socket qw(IPPROTO_TCP TCP_NODELAY);
use POE qw(Component::Server::TCP Component::Client::TCP Filter::Block Filter::Stream);
use Time::HiRes qw/gettimeofday tv_interval/;
use IO::Interface::Simple;
use IO::Socket::INET;
use IO::Socket;
use MIME::Base64;

my $sessions = {};
my $doCrypt = 0;
my $doPrepend = undef; # "abcdefghikjlmnopqrstuvwxyz";
my $doBase64 = 0;
my $printdebug = 0;

$| = 1;
my $looktime = 5;
my $nodeadpeer = 0;
my $debug = 0;
my $up = 0;
#my $MEXRETRYRESEND = 20;

use constant TUN_MAX_FRAME => 4096;

# Ioctl defines
use constant TUNSETNOCSUM => 0x400454c8;
use constant TUNSETDEBUG => 0x400454c9;
use constant TUNSETIFF => 0x400454ca;
use constant TUNSETPERSIST => 0x400454cb;
use constant TUNSETOWNER => 0x400454cc;

# TUNSETIFF ifr flags
use constant IFF_TUN   => 0x0001;
use constant IFF_TAP   => 0x0002;
use constant IFF_NO_PI => 0x1000;
use constant IFF_ONE_QUEUE => 0x2000;
use constant TUN_PKT_STRIP => 0x0001;

use constant STRUCT_IFREQ => 'Z16 s';
use constant TUNNEL_DEVICE => '/dev/net/tun';

my $name = 'tun%d';
my $tuntapsession = undef;

my $config = {};
my $seen = {};
my $lastseen = {};

open(CONFIG, "<", $ARGV[0] || "/etc/multivpn.cfg") || die "Config not found: ".$!;
while(<CONFIG>) {
   chomp;
   s,\#.*$,,gi;
   next if m,^\s*$,;
   my @config = split(/\t/, $_);
   if ($config[0] && (lc($config[0]) eq "link")) {
      $config->{links}->{$config[1]} = {
         name    => $config[1],
         src     => $config[2],
         srcport => $config[3],
         dstip   => $config[4] || undef,
         dstport => $config[5] || undef,
         factor  => $config[6],
         #curdstip => $config[4] || undef,
         lastdstip => $config[4] || undef,
         options => $config[7] || "",
         curip   => "",
      };
   } elsif($config[0] && (lc($config[0]) eq "local")) {
      $config->{local} = {
         ip   => $config[1],
         mask => $config[2] || 24,
         mtu  => $config[3] || 1300,
         dstip => $config[4],
         br    => $config[5],
      };
   } elsif($config[0] && (lc($config[0]) eq "route")) {
      push(@{$config->{route}}, {
         to => $config[1],
         mask => $config[2],
         gw => $config[3],
         table => $config[4],
         metric => $config[5],
      });
   } elsif(m,^\s*$,) {
   } else {
      die "Bad config line: ".$_;
   }
}
close(CONFIG);

sub fetchIPs {
   foreach my $curlink (keys %{$config->{links}}) {
      my $newsrcaddress = '';
      if (my $curif = IO::Interface::Simple->new($config->{links}->{$curlink}->{src})) {
         $newsrcaddress = $curif->address();
      } else {
         $newsrcaddress = $config->{links}->{$curlink}->{src};
      }
      my $restart = 0;
      if ($newsrcaddress && ($config->{links}->{$curlink}->{curip} ne $newsrcaddress)) {
         $config->{links}->{$curlink}->{curip} = $newsrcaddress;
         print "IP Change for ".$config->{links}->{$curlink}->{src}." !\n";
         $restart++;
      }
      #if ($config->{links}->{$curlink}->{lastdstip} ne $config->{links}->{$curlink}->{curdstip}) {
      #   $config->{links}->{$curlink}->{curdstip} = $config->{links}->{$curlink}->{lastdstip};
      #   print "DST Change for ".$config->{links}->{$curlink}->{src}." !\n";
      #   $restart++;
      #}
      if ($restart) {
         $poe_kernel->call($config->{links}->{$curlink}->{cursession} => "terminate")
            if $config->{links}->{$curlink}->{cursession};
         startUDPSocket($curlink);
      } else {
         $poe_kernel->post($config->{links}->{$curlink}->{cursession} => "Send" => "SES:".$curlink.":".join(",", keys %$lastseen))
            if $config->{links}->{$curlink}->{cursession} && ($config->{links}->{$curlink}->{dstip} || $config->{links}->{$curlink}->{lastdstip});
      }
   }
}

POE::Session->create(
   inline_states => {
      _start => sub {
         my ($kernel, $heap) = @_[KERNEL, HEAP];
         $kernel->yield("loop")
      },
      loop => sub {
         my ($kernel, $heap) = @_[KERNEL, HEAP];
         fetchIPs();
         $kernel->delay(loop => 1);
      },
   },
);

POE::Session->create(
   inline_states => {
      _start => sub {
         my ($kernel, $heap) = @_[KERNEL, HEAP];
         $kernel->yield("loop")
      },
      loop => sub {
         my ($kernel, $heap) = @_[KERNEL, HEAP];
         $lastseen = $seen;
         if (scalar(grep { $lastseen->{$_} } keys %$lastseen)) {
            doIf(1) unless $up;
            $up++;
         } else {
            doIf(0) if $up;
            $up = 0;
         }
         $seen = {};
         $kernel->delay(loop => 5);
      },
   },
);

sub doIf {
   my $up = shift;
   foreach my $curroute (@{$config->{route}}) {
      my $tmp = "ip route delete ".$curroute->{to}."/".$curroute->{mask}.(defined($curroute->{metric}) ? " metric ".$curroute->{metric} : "").($curroute->{table} ? " table ".$curroute->{table} : "");
      print $tmp."\n";
      system($tmp);
      $tmp = "ip route ".($up ? "add" : "delete")." ".$curroute->{to}."/".$curroute->{mask}." via ".$curroute->{gw}.(defined($curroute->{metric}) ? " metric ".$curroute->{metric} : "").($curroute->{table} ? " table ".$curroute->{table} : "");
      print $tmp."\n";
      system($tmp);
   }
}

sub startUDPSocket {
   my $link = shift;
   my $con = $config->{links}->{$link};
   #die "No curip: ".$con->{curip} unless $con->{curip};
   print "Starting ".$link." with source='".$con->{curip}."':".$con->{srcport}." and dst=".($con->{dstip}||"-").":".($con->{dstport}||"-")."\n";
   POE::Session->create(
      inline_states => {
         _start => sub {
            my ($kernel, $heap, $session, $con) = @_[KERNEL, HEAP, SESSION, ARG0];
            $heap->{con} = $con;
            my $bind  = ($con->{options} =~ m,bind,i)  ? 1 : 0;
            my $reuse = ($con->{options} =~ m,reuse,i) ? 1 : 0;
            print "Bind: ".$bind." Reuse:".$reuse." ".($con->{dstip}||"-").":".($con->{dstport}||"-")."\n";
            eval {
               $heap->{udp} = new IO::Socket::INET(
                  PeerAddr  => $bind ? $con->{dstip} : undef,
                  PeerPort  => $bind ? $con->{dstport} : undef,
                  LocalAddr => $con->{curip},
                  LocalPort => $con->{srcport},
                  ReuseAddr => $reuse ? 1 : 0,
                  #ReusePort => $reuse ? 1 : 0,
                  Proto     => 'udp',
               ) or die "ERROR in Socket Creation : $!\n";
            };
            if ($!) {
               print "Not possible: ".$!;
               return;
            } else {
               #$wheel->put({ payload => [ 'This datagram will go to the default address.' ], addr => '1.2.3.4', port => 13456 });
               if ($heap->{udp}) {
                  $heap->{sessionid} = $session->ID();
                  $sessions->{$heap->{sessionid}} = {
                     heap => $heap,
                     factor => $heap->{con}->{factor},
                     con => $con,
                  };
                  $kernel->select_read($heap->{udp}, "input");
                  if ($bind) {
                     unless (defined($heap->{udp}->send("a"))) {
                        print "PostBind not worked: ".$!."\n";
                     }
                  }
               } else {
                  my $retrytimeout = $config->{retrytimeout} || 30;
                  print "Binding to ".$con->{curip}.":".$con->{srcport}." not worked!\n";
               }
            }
            $con->{cursession} = $heap->{sessionid};
            #sleep(10);
         },
         _stop => sub {
            my ($kernel, $heap, $session) = @_[KERNEL, HEAP, SESSION];
            print "Session term.\n";
            delete $sessions->{$session->ID()};
         },
         input => sub {
            my ($kernel, $heap, $session) = @_[KERNEL, HEAP, SESSION];
            #print $input."\n";
            my $curinput = undef;
            while (defined($heap->{udp}->recv($curinput,1600))) {
               $heap->{con}->{lastdstip}   = $heap->{udp}->peerhost();
               $heap->{con}->{lastdstport} = $heap->{udp}->peerport();
               print "Incoming datagram from '".length($curinput)."' Bytes\n"
                  if $printdebug;
               if ($doPrepend) {
                  substr($curinput, 0, length($doPrepend), "");
               }
               if ($doCrypt) {
                  my $replace = substr($curinput, 0, 200, "");
                  $replace = join("", map { chr(((ord($_)+129) % 256)) } split(//, $replace));
                  $curinput = $replace.$curinput;
               }
               if ($doBase64) {
                  #print "PRE:".join(",", map { ord($_ ) } split(//, $curinput))."\n";
                  $curinput = decode_base64($curinput);
                  #print "POST:".join(",", map { ord($_ ) } split(//, $curinput))."\n";
               }
               if (!$nodeadpeer && (substr($curinput, 0, 4) eq "SES:")) {
                  my $announcement = [split(":", $curinput)];
                  shift(@$announcement);
                  my $dstlink = shift(@$announcement);
                  $config->{$dstlink}->{lastdstip} = $heap->{con}->{lastdstip};
                  $config->{$dstlink}->{lastdstport} = $heap->{con}->{lastdstport};
                  my $myseen = [];
                  if (my $tmp = shift(@$announcement)) {
                     $myseen = [split(",", $tmp)];
                  }
                  $seen->{$dstlink} = scalar(@$myseen);
                  foreach my $curlink (keys %{$config->{links}}) {
                     $config->{links}->{$curlink}->{active} = scalar(grep { $curlink eq $_ } @$myseen) ? 1 : 0;
                  }
                  print "Session announcement ".length($curinput)." bytes: ".$dstlink." and seen links ".join(",", @$myseen)."\n";
               } else {
                  $kernel->call($tuntapsession => "data", $curinput)
                     if $tuntapsession;
               }
            }
         },
         Send => sub {
            my ($kernel, $heap, $input) = @_[KERNEL, HEAP, ARG0];
            #print "Sending ".length($input)." Bytes via UDP to ".$heap->{con}->[0].":".$heap->{con}->[1].".\n";
            my $to = undef;
            if ($heap->{con}->{dstip} && $heap->{con}->{dstport}) {
               if (my $dstip = inet_aton($heap->{con}->{dstip})) {
                  $to = pack_sockaddr_in($heap->{con}->{dstport}, $dstip);
               } else {
                  print "Unable to reslove ".$heap->{con}->{dstip}."\n";
               }
            } elsif($heap->{con}->{lastdstip} && $heap->{con}->{lastdstport}) {
               if (my $dstip = inet_aton($heap->{con}->{lastdstip})) {
                  $to = pack_sockaddr_in($heap->{con}->{lastdstport}, inet_aton($heap->{con}->{lastdstip}));
               } else {
                  print "Unable to reslove ".$heap->{con}->{lastdstip}."\n";
               }
            }
            if ($to) {
               my $count = 0;
               #while
               if ($doBase64) {
                  $input = encode_base64($input, "");
               }
               if ($doCrypt) {
                  my $replace = substr($input, 0, 200, "");
                  $replace = join("", map { chr(((ord($_)+127) % 256)) } split(//, $replace));
                  $input = $replace.$input;
               }
               if ($doPrepend) {
                  $input = $doPrepend.$input;
               }
               if (!defined($heap->{udp}->send($input, 0, $to))) {
                  print "X";
                  #select(undef, undef, undef, 0.1);
                  #last if ($count++ > $MEXRETRYRESEND);
               }
            } else { 
               print $heap->{con}->{name}.": Cannot send: no dst ip/port.\n";
            }
         },
         terminate => sub {
            my ($kernel, $heap, $session) = @_[KERNEL, HEAP, SESSION];
            print "SOcket terminated.\n";
            delete $sessions->{$session->ID()};
            $kernel->select_read($heap->{udp});
            close($heap->{udp});
            delete $heap->{udp};
         },
      },
      args => [ $con ],
   );
}

POE::Session->create(
   inline_states => {
      _start => sub {
         my ($kernel, $heap) = @_[KERNEL, HEAP];
         $heap->{fh} = new IO::File(TUNNEL_DEVICE, 'r+') or die "Can't open ".TUNNEL_DEVICE.": $!";
         $heap->{ifr} = pack(STRUCT_IFREQ, $name||'', ($config->{local}->{ip} =~ m,^[\d\.]+$,) ? IFF_TUN : IFF_TAP);
         ioctl $heap->{fh}, TUNSETIFF, $heap->{ifr} or die "Can't ioctl() tunnel: $!";
         $heap->{interface} = unpack STRUCT_IFREQ, $heap->{ifr};
         print "Interface ".$heap->{interface}." up!\n";
         if ($config->{local}->{ip} =~ m,^[\d\.]+$,) {
            system("ifconfig ".$heap->{interface}." ".$config->{local}->{ip}."/".$config->{local}->{mask}." up");
         } else {
            system("ifconfig ".$heap->{interface}." up");
            system("brctl", "addif", $config->{local}->{ip}, $heap->{interface});
         }
         system("ifconfig ".$heap->{interface}." dstaddr ".$config->{local}->{dstip})
            if ($config->{local}->{dstip});
         system("iptables -A FORWARD -o ".$heap->{interface}." -p tcp -m tcp --tcp-flags SYN,RST SYN -m tcpmss --mss ".($config->{local}->{mtu}-40).":65495 -j TCPMSS --clamp-mss-to-pmtu")
            if ($config->{local}->{mtu});
         system("ifconfig ".$heap->{interface}." mtu ".$config->{local}->{mtu});
         $kernel->select_read($heap->{fh}, "got_input");
         $tuntapsession = $_[SESSION];
      },
      got_input => sub {
         my ($kernel, $heap, $socket) = @_[KERNEL, HEAP, ARG0];
         die if ($socket != $heap->{fh});
         while (sysread($heap->{fh}, my $buf = "", TUN_MAX_FRAME)) {
            foreach my $sessid (sort {
               ($sessions->{$a}->{tried}||0) <=>
               ($sessions->{$b}->{tried}||0)
            } keys %$sessions) {
               $sessions->{$sessid}->{tried} += (1 / $sessions->{$sessid}->{factor}) if $sessions->{$sessid}->{factor};
               next unless ($nodeadpeer || $sessions->{$sessid}->{con}->{active});
               $_[KERNEL]->call($sessid => "Send" => $buf);
               last;
            }
         }
      },
      data => sub {
         my ($kernel, $heap, $buf) = @_[KERNEL, HEAP, ARG0];
         my $size = syswrite($heap->{fh}, $buf);
         print $size." != ".length($buf)."\n"
         #die $size." != ".length($buf)
            unless ($size == length($buf));
      },
    }
  );

$poe_kernel->run();

sub nagle(*;$) {
   my $fh = shift;
   if (shift) {
      setsockopt($fh, IPPROTO_TCP, TCP_NODELAY, 0) || print "Couldn't enable Nagle's algorithm: $!\n";
   } else {
      setsockopt($fh, IPPROTO_TCP, TCP_NODELAY,1) || print "Couldn't disable Nagle's algorithm: $!\n";
   }
}

sub doReadWrite {
   my $readWrite = shift;
   my $put = shift;
   my $error_handler = shift;
   if (defined($readWrite) && 
         ((ref($readWrite) eq "POE::Wheel::ReadWrite") ||
          (ref($readWrite) eq "POE::Wheel::UDP"))) {
      $readWrite->put($put) && $error_handler && $poe_kernel->yield($error_handler) if $put;
      return 1;
   } else {
      print "Not a ReadWrite: ".ref($readWrite)."\n";
   }
   return 0;
}

sub printDebug {
    print "\n".join("\t", map { $_."=".($sessions->{$_}->{high}||"-").
                              "(".($sessions->{$_}->{outcount}||"-")."/".
                               "".($sessions->{$_}->{curoutcount}||"-")."/".
                               "".($sessions->{$_}->{tried}||"-").")" }  keys %$sessions)."\n";
}
