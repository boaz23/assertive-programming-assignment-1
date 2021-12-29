method Main() {
	var x := ComputeGCD(8, 12);
	assert x == 4 by {
		assert CommonDivisor(8, 12, 4);
		assert forall x :: x > 4 ==> !CommonDivisor(8, 12, x);
	}
	print "GCD(8,12)=";
	print x;
	x := ComputeGCD(15, 6);
	assert x == 3 by {
		assert CommonDivisor(15, 6, 3);
		assert forall x :: x > 3 ==> !CommonDivisor(15, 6, x);
	}
	print "\nGCD(15,6)=";
	print x;
	x := ComputeGCD(10, 30);
	assert x == 10 by {
		assert CommonDivisor(10, 30, 10);
		assert forall x :: x > 10 ==> !CommonDivisor(10, 30, x);
	}
	print "\nGCD(10,30)=";
	print x;
	x := ComputeGCD(30, 10);
	assert x == 10 by {
		assert CommonDivisor(30, 10, 10);
		assert forall x :: x > 10 ==> !CommonDivisor(30, 10, x);
	}
	print "\nGCD(30,10)=";
	print x;
	x := ComputeGCD(100, 101);
	assert x == 1;
	print "\nGCD(100,101)=";
	print x;
}

predicate CommonDivisor(a: nat, b: nat, c: nat)
{
	c > 0 && a%c == b%c == 0
}

predicate GreatestCommonDivisor(a: nat, b: nat, c: nat)
{
	CommonDivisor(a, b, c) &&
	forall d: nat :: CommonDivisor(a, b, d) ==> d <= c
}

method ComputeGCD(a: nat, b: nat) returns (i: nat)
	requires a > 0 && b > 0
	ensures GreatestCommonDivisor(a, b, i)
