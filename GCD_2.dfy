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

// :verify false
lemma {:axiom} MultiplyThenDivideIsId()
	ensures forall a, b: nat :: b != 0 ==> (b * a) / b == a

function Remainder_Definition(a: nat, b: nat): (nat, nat)
	requires b != 0
{
	(a / b, a % b)
}

predicate Remainder_EqualsFirst(a: nat, b: nat)
	requires b != 0
{
	var (q, r) := Remainder_Definition(a, b);
	a == (q * b) + r
}

lemma Remainder_Specific(a: nat, b: nat)
	requires b != 0
	ensures Remainder_EqualsFirst(a, b)
{
}

lemma ModMultipleIsZero(c: nat)
	requires c != 0
	ensures forall a: nat :: (c * a) % c == 0
{
	MultiplyThenDivideIsId();
}

lemma {:verify true} CommonDivisorPersists_AfterMod(a: nat, b: nat, c: nat)
	requires b > 0
	requires CommonDivisor(a, b, c)
	ensures CommonDivisor(b, a % b, c)
{
	calc {
		(a % b) % c;
		== { Remainder_Specific(a, b); }
		(a - ((a / b) * b)) % c;
		== {
			Remainder_Specific(a, c);
			Remainder_Specific(b, c);
		}
		(
			((a/c)*c + (a%c)) - // == a
			(a/b) * (
				(b/c)*c + (b%c) // == b
			)
		) % c;
		== { assert CommonDivisor(a, b, c); }
		((a/c)*c - (a/b)*(b/c)*c) % c;
		== // Multiplication distributaion
		(c * ((a / c) - (a / b) * (b / c))) % c;
		== { ModMultipleIsZero(c); }
		0;
	}
}

lemma {:verify true} CommonDivisorPersists_BeforeMod(a: nat, b: nat, c: nat)
	requires b > 0
	requires CommonDivisor(b, a % b, c)
	ensures CommonDivisor(a, b, c)
{
	calc {
		a % c;
		==  { Remainder_Specific(a, b); }
		(((a / b) * b) + (a % b)) % c;
		== {
			Remainder_Specific(a % b, c);
			Remainder_Specific(b, c);
		}
		(
			(a/b) * (
				(b/c)*c + (b%c) // == b
			) + (
				((a%b)/c)*c + ((a%b)%c) // == (a % b)
			)
		) % c;
		== { assert CommonDivisor(b, a % b, c); }
		((a/b)*(b/c)*c + ((a%b)/c)*c) % c;
		== // Multiplication distributaion
		(c * ((a/b)*(b/c) + (a%b)/c)) % c;
		== { ModMultipleIsZero(c); }
		0;
	}
}

lemma {:verify true} CommonDivisorPersists(a: nat, b: nat)
	requires b > 0
	ensures forall c: nat :: CommonDivisor(a, b, c) <==> CommonDivisor(b, a % b, c)
{
	forall c: nat | true ensures CommonDivisor(a, b, c) <==> CommonDivisor(b, a % b, c)
	{
		if (CommonDivisor(a, b, c)) {
			CommonDivisorPersists_AfterMod(a, b, c);
		}
		if (CommonDivisor(b, a % b, c)) {
			CommonDivisorPersists_BeforeMod(a, b, c);
		}
	}
}

lemma {:verify true} GcdInvariantStepProof(a: nat, b: nat)
	requires a > 0 && b > 0
	ensures forall c: nat :: GreatestCommonDivisor(a, b, c) <==> GreatestCommonDivisor(b, a % b, c)
{
	CommonDivisorPersists(a, b);
}

method ComputeGCD(a: nat, b: nat) returns (i: nat)
	requires a > 0 && b > 0
	ensures GreatestCommonDivisor(a, b, i)
{
	var a1 := a;
	var b1 := b;
	ghost var a1_prev := a;
	ghost var b1_prev := b;

	while (b1 != 0)
		invariant a1_prev > 0 && b1_prev > 0
		invariant forall d: nat :: GreatestCommonDivisor(a, b, d) <==> GreatestCommonDivisor(a1_prev, b1_prev, d)
		invariant forall d: nat :: GreatestCommonDivisor(a1_prev, b1_prev, d) <==> GreatestCommonDivisor(a1, b1, d)
		decreases b1
	{
		assert b1 > 0; // This is necessary for dafny to recognize this. Do not remove.
		a1_prev, b1_prev := a1, b1;
		GcdInvariantStepProof(a1_prev, b1_prev);
		b1, a1 := a1 % b1, b1;
	}

	i := a1;
}
