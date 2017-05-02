#! /bin/bash

TIMEOUT=5
EXEC_OPTION=$1

arr=()
fail=()
cd tests/secd_tests
i=0
k=0
for t in *.fo ../*.fo; do
  k=$(($k+1))
  echo "Going forward with test $(echo $t | sed 's/\.\.\///g')..."
  ( ../../fouine $EXEC_OPTION $t ) & pid=$!
  (sleep $TIMEOUT && kill -HUP $pid) 2>/dev/null & watcher=$!
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
  echo "----------------"
done

echo "Done testing with $i/$k successful tests :"
echo ""
echo "Successful tests are :"
for t in ${arr[@]}; do
  echo $t
done
echo ""
echo "Failed tests are :"
for t in ${fail[@]}; do
  echo $t
done
