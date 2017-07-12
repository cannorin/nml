#!/bin/sh

for f in examples/*.nml; do 
  echo "---------- $f ----------"
  mono bin/Debug/nmli.exe $f
  echo ""
  echo "Press enter to continue .."
  read dummy > /dev/null
done

