#! /bin/bash
# 
# Bash script for testing Fouine codes in the tests/ dir
# Takes exec options for ./fouine as parameters.

TIMEOUT=50
EXEC_OPTION=$@


arr=()
fail=()
cd src/tests
i=0
k=0
for t in *.fo ; do
    k=$(($k+1))
    echo "Going forward with test $(echo $t | sed 's/\.\.\///g')..."
    ( ../fouine $EXEC_OPTION $t 2> erreur) & pid=$!
    (sleep $TIMEOUT && kill -HUP $pid) 2>/dev/null & watcher=$!
    if [[ -s erreur ]]; then
        echo "Test terminated (exceptions occured)"
        fail+=("$(echo $t | sed 's/\.\.\///g')")
    else
        if wait $pid 2>/dev/null; then
            echo ""
            echo "Test successful !"
            arr+=("$(echo $t | sed 's/\.\.\///g')")
            i=$(($i+1))
            pkill -HUP -P $watcher
            wait $watcher
        else
            echo "Test terminated (timeout $TIMEOUT s)"
            fail+=("$(echo $t | sed 's/\.\.\///g')")
        fi
    fi
    echo "----------------"
    read -n 1 -s -p "Press any key to continue\n"
done

#Stupid/doesn't work
#echo "Done testing with $i/$k successful tests :"
#echo ""
#echo "Successful tests are :"
#for t in ${arr[@]}; do
#    echo $t
#done
#echo ""
#echo "Failed tests are :"
#for t in ${fail[@]}; do
#    echo $t
#done