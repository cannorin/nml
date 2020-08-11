#!/bin/bash

script_dir=$(cd $(dirname ${BASH_SOURCE:-$0}); pwd)
mkdir -p $script_dir/.dotnet
if [ ! -f "${script_dir}/.dotnet/dotnet" ]; then
  wget "https://download.visualstudio.microsoft.com/download/pr/c1a30ceb-adc2-4244-b24a-06ca29bb1ee9/6df5d856ff1b3e910d283f89690b7cae/dotnet-sdk-3.1.302-linux-x64.tar.gz"
  tar xzf dotnet-sdk-3.1.302-linux-x64.tar.gz -C "${script_dir}/.dotnet"
  rm xzf dotnet-sdk-3.1.302-linux-x64.tar.gz
fi
export DOTNET_CLI_TELEMETRY_OPTOUT=1
export DOTNET_PATH="${script_dir}/.dotnet"
make run