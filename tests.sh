echo "Which machine do you want to try ? [I for interpreter/ S for SECD]"
read a

if [ $a == "I" ]; then
  sh testing.sh
elif [ $a == "S" ]; then
  sh testing_secd.sh
else
  echo "Wrong argument"
fi
