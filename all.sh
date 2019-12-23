#!/bin/sh
for i in `ls *.ls`
do
	case $i in
		prelude.ls)
			;;
		proto.ls)
			./target/debug/lofer-lang $i || exit
			;;
		*)
			./target/debug/lofer-lang prelude.ls $i || exit
			;;
	esac
done
