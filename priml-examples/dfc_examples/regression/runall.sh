#!/bin/sh

echo "" > out.txt
for file in *.prm
do
    echo -n "$file\t" >> out.txt
    /usr/bin/time --quiet -a -o out.txt -f "%x\t%e" ../../../primlc $file out > /dev/null 2> /dev/null
done
