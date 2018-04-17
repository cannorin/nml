#!/bin/sh

for f in examples/*.nml; do 
  echo "---------- $f ----------"
  dotnet bin/Debug/netcoreapp2.0/nmli.dll $f
  echo ""
  echo "Press enter to continue .."
  read dummy > /dev/null
done

