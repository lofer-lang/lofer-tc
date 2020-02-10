#!/bin/sh

./target/debug/lofer-lang proto.ls || exit

for i in church-list.ls inverse.ls test.ls type-in-type.ls
do
	./target/debug/lofer-lang prelude.ls $i || exit
done

for i in negative_extras.ls ind-safety-theorem.ls inductive-church.ls
do
	./target/debug/lofer-lang prelude.ls negative.ls $i || exit
done

./target/debug/lofer-lang prelude.ls rec.ls mutual-rec.ls || exit

for i in overload-test.ls fix-test.ls
do
	./target/debug/lofer-lang prelude.ls rec.ls data.ls nat.ls list.ls eq.ls $i || exit
done

./target/debug/lofer-lang prelude.ls rec.ls data.ls eq.ls weak.ls

./target/debug/lofer-lang prelude.ls rec.ls signed.ls data.ls nat.ls int.ls rat.ls eq.ls num-tests.ls

