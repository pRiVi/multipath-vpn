Multipath-VPN
=============

A tunneling VPN client and server, which supports failover and multiple connections via the linux tuntap interface.


## Install

### On client
```bash
git clone https://github.com/privi/multipath-vpn

# installing the required perl modules:
cpan POE::Wheel::UDP IO::Interface::Simple

# copy the config
cp dynIpClient.example.cfg /etc/multivpn.cfg
```
Edit the config conforming to your network setup.

### On server 
```bash
git clone https://github.com/privi/multipath-vpn

# installing the required perl modules:
cpan POE::Wheel::UDP IO::Interface::Simple

# copy the config
cp serverStaticIP.example.cfg /etc/multivpn.cfg
```
Edit the config conforming to your network setup.
