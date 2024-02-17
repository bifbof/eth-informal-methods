#!/bin/sh

# student number: 17-932-161
# I got pretty confused about how to use variables in a shell script.
# So I go the very stupid but nonetheless effective way in storing everything
# in files. Hope that is okay :D

if [ ! -d "temp" ]; then
    mkdir "temp"
else
    echo "Would override directory 'temp', please delete manually"
    exit
fi
f1="./temp/temp1.txt"
f2="./temp/temp2.txt"
f3="./temp/temp3.txt"

# produce correspondence of two files
nl $1 | sort -b -k 2 > "$f1" 
nl $2 | sort -b -k 2 > "$f2"
# join on the lines and output line-index pairs
join -o 1.1,2.1 -1 2 -2 2 "$f1" "$f2" > "$f3"

sort -k 1,1 -k 2,2r "$f3" | awk '{print $2}' > "$f2"
python3 upsequence.py < "$f2" > "$f1"

# output lines that occure in longest common subsequence
nl $2 > "$f2"
join -o 1.2 -1 1 -2 1 "$f2" "$f1"

# cleanup
rm "temp" -fr
