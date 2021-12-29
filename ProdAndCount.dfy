method Main() {
	var q := [7, -2, 3, -2];

	var p, c := ProdAndCount(q, -2);
	print "The product of all positive elements in [7,-2,3,-2] is ";
	print p;
	assert p == RecursivePositiveProduct(q) == 21;
	print "\nThe number of occurrences of -2 in [7,-2,3,-2] is ";
	print c;
	assert c == RecursiveCount(-2, q) == 2 by {
		calc {
			RecursiveCount(-2, q);
		== { assert q[3] == -2; AppendOne(q, 3); }
			1 + RecursiveCount(-2, q[..3]);
		== { assert q[2] != -2; AppendOne(q, 2); }
			1 + RecursiveCount(-2, q[..2]);
		== { assert q[1] == -2; AppendOne(q, 1); }
			1 + 1 + RecursiveCount(-2, q[..1]);
		== { assert q[0] != -2; AppendOne(q, 0); }
			1 + 1 + RecursiveCount(-2, q[..0]);
		}
	}
}

lemma AppendOne<T>(q: seq<T>, n: nat)
	requires n < |q|
	ensures q[..n]+[q[n]] == q[..n+1]
{}

function RecursivePositiveProduct(q: seq<int>): int
	decreases |q|
{
	if q == [] then 1
	else if q[0] <= 0 then RecursivePositiveProduct(q[1..])
	else q[0] * RecursivePositiveProduct(q[1..])
}

function RecursiveCount(key: int, q: seq<int>): int
	decreases |q|
{
	if q == [] then 0
	else if q[|q|-1] == key then 1+RecursiveCount(key, q[..|q|-1])
	else RecursiveCount(key, q[..|q|-1])
}

method ProdAndCount(q: seq<int>, key: int) returns (prod: int, count: nat)
	ensures prod == RecursivePositiveProduct(q)
	ensures count == RecursiveCount(key, q)
