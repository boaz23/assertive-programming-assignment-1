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
lemma Remainder_Forall()
	ensures forall a, b : nat :: b != 0 ==> Remainder_EqualsFirst(a, b)
{
}
lemma Remainder_Specific(a: nat, b: nat)
	requires b != 0
	ensures Remainder_EqualsFirst(a, b)
{
}

lemma {:axiom} MultiplyThenDivideIsId()
	ensures forall a, b : nat :: b != 0 ==> (b * a) / b == a

lemma ModMultipleIsZero(c: nat)
	requires c != 0
	ensures forall a: nat :: (c * a) % c == 0
{
	MultiplyThenDivideIsId();
}

function RemaindersN(a: nat, b: nat): int
	requires a > 0
	decreases b
	ensures RemaindersN(a, b) >= -1
{
	if b == 0 then -1
	else 1 + RemaindersN(b, a % b)
}

function RemainderK(a: nat, b: nat, k: int): nat
	requires a > 0
	requires -2 <= k <= RemaindersN(a, b)
	decreases b
{
	if k == -2 then a
	else if k == -1 then b
	else if b == 0 then a
	else RemainderK(b, a % b, k - 1)
}

lemma {:verify false} RemainderK_WhenZeroSpecification(a: nat, b: nat)
	requires a > 0 && b > 0
	ensures RemainderK(a, b, RemaindersN(a, b)) == 0
	ensures forall k : nat :: k < RemaindersN(a, b) ==> RemainderK(a, b, k) > 0
{
}

// lemma {:verify false} RemainderK_WhenZeroIff(a: nat, b: nat)
// 	requires a > 0 && b > 0
// 	ensures forall k : nat :: k == RemaindersN(a, b) <==> RemainderK(a, b, k) == 0
// 	// ensures k == RemaindersN(a, b) + 1 <==> RemainderK(a, b, k - 1) == 0
// {
// }

lemma {:verify false} RemaindersN_NonNegative(a: nat, b: nat)
	requires a > 0 && b > 0
	ensures RemaindersN(a, b) >= 0
{
}

lemma {:verify false} K_LessThan_N(a: nat, b: nat, k: nat)
	requires a > 0 && b > 0
	requires 0 <= k <= RemaindersN(a, b) + 1
	requires r_k_m1_neq_0: RemainderK(a, b, k - 1) != 0
	ensures k + 1 <= RemaindersN(a, b) + 1
{
}

lemma {:verify false} NextRemainerK(a: nat, b: nat, k: int)
	requires a > 0 && b > 0
	requires 0 <= k <= RemaindersN(a, b)
	ensures RemainderK(a, b, k) == RemainderK(a, b, k - 2) % RemainderK(a, b, k - 1)
{
}

lemma {:verify false} RemainderNm1IsGcd(a: nat, b: nat)
	requires a > 0 && b > 0
	ensures GreatestCommonDivisor(a, b, RemainderK(a, b, RemaindersN(a, b) - 1))
{
}

method ComputeGCD(a: nat, b: nat) returns (i: nat)
	requires a > 0 && b > 0
	ensures GreatestCommonDivisor(a, b, i)
{
	// k counts the iteration number (starts with 0, zero-based).
	// r_-2 == a, r_-1 == b
	ghost var k : nat := 0;
	ghost var N : int := RemaindersN(a, b);
	var r_k_m2 := a;
	var r_k_m1 := b;

	RemaindersN_NonNegative(a, b);
	while (r_k_m1 != 0)
		invariant k <= N + 1
		invariant r_k_m2 == RemainderK(a, b, k - 2)
		invariant r_k_m1 == RemainderK(a, b, k - 1)
		decreases r_k_m1
	{
		K_LessThan_N(a, b, k);
		NextRemainerK(a, b, k);
		assert k + 1 <= N + 1;
		assert r_k_m1 == RemainderK(a, b, (k + 1) - 2);
		assert r_k_m2 % r_k_m1 == RemainderK(a, b, (k + 1) - 1);

		r_k_m1, r_k_m2 := r_k_m2 % r_k_m1, r_k_m1;

		assert k + 1 <= N + 1;
		assert r_k_m2 == RemainderK(a, b, (k + 1) - 2);
		assert r_k_m1 == RemainderK(a, b, (k + 1) - 1);

		k := k + 1;
		
		assert k <= N + 1;
		assert r_k_m2 == RemainderK(a, b, k - 2);
		assert r_k_m1 == RemainderK(a, b, k - 1);
	}

	assert k == N + 1 by {
		assert r_k_m1 == RemainderK(a, b, k - 1) == 0;
		RemainderK_WhenZeroSpecification(a, b);
	}
	assert GreatestCommonDivisor(a, b, r_k_m2) by {
		RemainderNm1IsGcd(a, b);
	}

	// assert k == N;
	// assert r_k_m3 == RemainderK(a, b, N - 3) && r_k_m2 == RemainderK(a, b, N - 2) && r_k_m1 == RemainderK(a, b, N - 1);
	// // assert exists q_k : nat :: r_k_m3 == q_k*r_k_m2 + r_k_m1;
	// assert r_k_m1 == 0;
	// assert r_k_m3 % r_k_m2 == r_k_m1 == 0;
	i := r_k_m2;
}
