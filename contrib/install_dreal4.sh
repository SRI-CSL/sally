#!/bin/bash
set -e 

# dreal
sudo apt-get install curl
UBUNTU_VERSION=$(lsb_release -rs)
echo Getting dReal for $UBUNTU_VERSION
curl -fsSL https://raw.githubusercontent.com/dreal/dreal4/master/setup/ubuntu/$UBUNTU_VERSION/install.sh | sudo bash

 