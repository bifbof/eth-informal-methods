# student number: 17-932-161
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
# add line number to lines
# then sort lexicographically by the line
nl $1 | sort -b -k 2 > "$f1" 
nl $2 | sort -b -k 2 > "$f2"

# join the lines on matching lines
# then output only line numbers of both
join -o 1.1,2.1 -1 2 -2 2 "$f1" "$f2"
rm "temp" -fr
