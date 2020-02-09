#!/bin/sh
for i in `ls *.ls`
do
	case $i in
		prelude.ls)
			;;
		proto.ls)
			./target/debug/lofer-lang $i || exit
			;;
		negative_extras.ls | ind-safety-theorem.ls | inductive-church.ls)
			./target/debug/lofer-lang prelude.ls negative.ls $i || exit
			;;
		mutual-rec.ls)
			./target/debug/lofer-lang prelude.ls rec.ls $i || exit
			;;
		nat.ls | list.ls)
			./target/debug/lofer-lang prelude.ls rec.ls data.ls $i || exit
			;;
		weak.ls)
			./target/debug/lofer-lang prelude.ls rec.ls data.ls eq.ls $i || exit
			;;
		overload-test.ls | fix-test.ls | int.ls)
			./target/debug/lofer-lang prelude.ls rec.ls data.ls nat.ls eq.ls $i || exit
			;;
		*)
			./target/debug/lofer-lang prelude.ls $i || exit
			;;
	esac
done
