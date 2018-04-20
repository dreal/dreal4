#!/bin/bash
set -euo pipefail

# Needed for Travis-CI
# From https://groups.google.com/d/msg/bigbluebutton-setup/cVKn5fl_01E/JfPzTzziDgAJ
sudo apt-key list | \
 grep "expired: " | \
 sed -ne 's|pub .*/\([^ ]*\) .*|\1|gp' | \
 xargs -n1 sudo apt-key adv --keyserver hkp://keyserver.ubuntu.com:80 --recv-keys
