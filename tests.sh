echo "Which machine do you want to try ? [I for interpreter/ S for SECD / Z for ZINC]"
read a

if [ $a == "S" ]; then
  sh testing_secd.sh
elif [ $a == "Z" ]; then
  sh testing_zinc.sh
else
  sh testing.sh
fi
