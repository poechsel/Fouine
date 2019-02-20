#! /bin/bash

TIMEOUT=5
EXEC_OPTION="-machine S"

arr=()
fail=()
cd tests/programs
i=0
k=0
for t in *.fo ../*.fo; do
  k=$(($k+1))
  echo ""
  echo "Executing test file $(echo $t | sed 's/\.\.\///g')..."; sleep 0.1
  ( ../../fouine $EXEC_OPTION $t ) & pid=$!; sleep 0.1
  (sleep $TIMEOUT && kill -HUP $pid) 2>/dev/null & watcher=$!
  if wait $pid 2>/dev/null; then
    echo ""
    echo "Test successful !"; sleep 0.2
    arr+=("$(echo $t | sed 's/\.\.\///g')")
    i=$(($i+1))
    pkill -HUP -P $watcher
    wait $watcher
  else
    echo "Test terminated (timeout $TIMEOUT s)"; sleep 0.2
    fail+=("$(echo $t | sed 's/\.\.\///g')")
  fi
  echo ""; echo "==================="; echo ""; sleep 0.1
  read -n 1 -s -p "Press any key to continue"
  echo ""; echo ""; echo "==================="
done

#echo "Done testing with $i/$k successful tests :"
#echo ""
#echo "Successful tests are :"
#for t in ${arr[@]}; do
#  echo $t
#done
#echo ""
#echo "Failed tests are :"
#for t in ${fail[@]}; do
#  echo $t
#done
