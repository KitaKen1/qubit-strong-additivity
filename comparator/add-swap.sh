#!/usr/bin/env bash
# Add swap space: at most the first argument (in GB), and never so much that less than the second
# argument (in GB, default 4) stays free on the chosen disk (/mnt when it is a separate disk with more
# room, otherwise /).
set -eu
want=$1 keep=${2:-4}
free_gb() { df --output=avail -BG "$1" | tail -1 | tr -dc 0-9; }
dir=/
if mountpoint -q /mnt && [ "$(free_gb /mnt)" -gt "$(free_gb /)" ]; then dir=/mnt; fi
gb=$(( $(free_gb "$dir") - keep ))
[ "$gb" -gt "$want" ] && gb=$want
if [ "$gb" -lt 1 ]; then echo "no room for swap on $dir"; exit 0; fi
file="${dir%/}/swap-extra-$RANDOM"
sudo fallocate -l "${gb}G" "$file"
sudo chmod 600 "$file"
sudo mkswap "$file" > /dev/null
sudo swapon "$file"
echo "added ${gb} GB of swap on $dir"
{ free -g; swapon --show; } | tee -a "$RUNNER_TEMP/runner.txt"
