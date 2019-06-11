#!/bin/bash
set -e 

# dreal
sudo apt-get install curl
curl -fsSL https://raw.githubusercontent.com/dreal/dreal4/master/setup/ubuntu/$(lsb_release -rs)/install.sh | sudo bash

 