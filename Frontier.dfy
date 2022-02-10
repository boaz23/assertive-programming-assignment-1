datatype BT<T> = Tip(T) | Node(BT<T>, BT<T>)

class IO<T> {
	var alpha: seq<T>, omega: seq<T>;

	method Input() returns (x: T)
		requires !EOF() // alpha != []
		modifies this
		ensures omega == old(omega)
		ensures old(alpha) == [x] + alpha
	{
		x, alpha := alpha[0], alpha[1..];
	}

	method Output(x: T)
		modifies this
		ensures alpha == old(alpha)
		ensures omega == old(omega) + [x]
	{
		omega := omega + [x];
	}

	method Rewrite()
		modifies this
		ensures omega == []
		ensures alpha == old(alpha)
	{
		omega := [];
	}

	predicate method EOF() reads this { alpha == [] }

}

method Main()
{
	var tree: BT<int>;
	tree := Tip(1);
	var io: IO<int>;
	io := new IO<int>;
	FrontierIter(tree, io);
	print io.omega;

	io.Rewrite();
	tree := Node(tree, Tip(2));
	FrontierIter(tree, io);
	print io.omega;
}

function Frontier<T>(tree: BT<T>): seq<T>
{
	match tree {
		case Tip(n) => [n]
		case Node(left, right) => Frontier(left) + Frontier(right)
	}
}

function Frontiers<T>(trees: seq<BT<T>>): seq<T>
{
	if trees == [] then [] else Frontier(trees[0]) + Frontiers(trees[1..])
}

// TODO: implement iteratively (with a loop),
// updating the value of "io.omega" through calls to "io.Output" for each "tip" of the tree;
// document each proof obligation, as we've learned, with assertion propagation and a lemma
method FrontierIter<T>(tree: BT<T>, io: IO<T>)
	modifies io
	ensures io.omega == old(io.omega) + Frontier(tree)
{
	// We chose to use a sequence because of the following (in no particular order):
	// 1. Trying to use an array which grows dynamically was giving us trouble.
	//    We didn't learn how to use an array as local variable.
	//    We lack `reads` and `modifies` permissions on the array to actually
	//    make use of it and we only saw how to do that when the array is passed
	//    as an argument to a method.
	//    And we can't do that because the pointer also has to change dynamically
	//    in order to grow dynamically which then implies it has to be a local variable.
	// 2. Problems with writing a function to calculate the maximum size
	//    will be used by the stack:
	//    1. It will be complex to prove to Dafny that the algorthim never exceeds the
	//       the array size.
	//    2. But not only that, an even bigger issue is that doing so will never
	//       acutally be done in practice because why do so when using an array which
	//       grows dynamically is efficient and is simpler.
	//       So doing so is just for the sake of doing so.

	// Why the stack grows towards the beginning rather than the end:
	// 1. We're using a sequence anyway so this doesn't matter.
	// 2. It makes an algorithm which is easier to prove it's correctness.
	// 3. It seems that you had that solution in mind when making this excerise,
	//    indicated by both the lecture and the `Frontiers` function which
	//    takes the first item of the sequence.

	var stack := [tree]; // grows towards the beginning of the sequence
	while stack != []
		invariant LoopInv(tree, stack, io.omega, old(io.omega))
		decreases ForestSize(stack)
	{
		ghost var s := stack;
		ghost var V0 := ForestSize(stack);

		assert s != [];
		assert LoopInv(tree, s, io.omega, old(io.omega));

		// This generates a compile error for some reason
		// var t;
		// t, stack := stack[0], stack[1..];
		var t := stack[0];
		stack := stack[1..];

		assert s == [t] + stack;
		assert LoopInv(tree, s, io.omega, old(io.omega));

		match t
		{
			case Tip(x) =>
			{
				assert s == [t] + stack;
				assert LoopInv(tree, s, io.omega, old(io.omega));
				assert t == Tip(x);
				// ==>?
				EnsureInvTip(tree, stack, s, t, x, io.omega, old(io.omega));
				assert LoopInv(tree, stack, io.omega + [x], old(io.omega)); // maintaining the loop invariant

				io.Output(x);
				assert LoopInv(tree, stack, io.omega, old(io.omega)); // maintaining the loop invariant
				assert 0 <= ForestSize(stack) < V0; // the loop termination
			}
			case Node(t1, t2) =>
			{
				assert s == [t] + stack;
				assert LoopInv(tree, s, io.omega, old(io.omega));
				assert t == Node(t1, t2);
				// ==>?
				EnsureInvNode(tree, stack, s, t, t1, t2, io.omega, old(io.omega));
				assert LoopInv(tree, [t1, t2] + stack, io.omega, old(io.omega));

				stack := [t1, t2] + stack;
				assert LoopInv(tree, stack, io.omega, old(io.omega)); // maintaining the loop invariant
				assert 0 <= ForestSize(stack) < V0; // the loop termination
			}
		}

		assert LoopInv(tree, stack, io.omega, old(io.omega)); // maintaining the loop invariant
		assert 0 <= ForestSize(stack) < V0; // the loop termination
	}

	assert LoopInv(tree, stack, io.omega, old(io.omega)); // from the loop invariant
	assert stack == []; // from the negation of the loop guard
	// ==>
	EnsurePostCondition(tree, stack, io.omega, old(io.omega));
	assert io.omega == old(io.omega) + Frontier(tree);
}

predicate LoopInv<T>(tree: BT<T>, forest: seq<BT<T>>, omega: seq<T>, old_omega: seq<T>)
{
	omega + Frontiers(forest) == old_omega + Frontier(tree)
}

function TreeSize<T>(tree: BT<T>): nat
	decreases tree
	ensures TreeSize(tree) >= 1
{
	match tree
	{
		case Tip(x) => 1
		case Node(t1, t2) => 1 + TreeSize(t1) + TreeSize(t2)
	}
}

function ForestSize<T>(forest: seq<BT<T>>): nat
	decreases forest
	ensures ForestSize(forest) >= 0
{
	if forest == [] then 0
	else TreeSize(forest[0]) + ForestSize(forest[1..])
}

lemma EnsureInvTip<T>(tree: BT<T>, stack: seq<BT<T>>, s: seq<BT<T>>, t: BT<T>, x: T, omega: seq<T>, old_omega: seq<T>)
	requires s == [t] + stack
	requires LoopInv(tree, s, omega, old_omega)
	requires t == Tip(x)
	
	ensures LoopInv(tree, stack, omega + [x], old_omega)
{
}

lemma EnsureInvNode<T>(tree: BT<T>, stack: seq<BT<T>>, s: seq<BT<T>>, t: BT<T>, t1: BT<T>, t2: BT<T>, omega: seq<T>, old_omega: seq<T>)
	requires s == [t] + stack
	requires LoopInv(tree, s, omega, old_omega)
	requires t == Node(t1, t2)
	
	ensures LoopInv(tree, [t1, t2] + stack, omega, old_omega)
{
}

lemma {:induction false} EnsurePostCondition<T>(tree: BT<T>, stack: seq<BT<T>>, omega: seq<T>, old_omega: seq<T>)
	requires LoopInv(tree, stack, omega, old_omega)
	requires stack == []

	ensures omega == old_omega + Frontier(tree)
{
}

// The cleaner version
method FrontierIter'<T>(tree: BT<T>, io: IO<T>)
	modifies io
	ensures io.omega == old(io.omega) + Frontier(tree)
{
	var stack := [tree]; // grows towards the beginning of the sequence
	while stack != []
		invariant LoopInv(tree, stack, io.omega, old(io.omega))
		decreases ForestSize(stack)
	{
		ghost var V0 := ForestSize(stack);
		var t := stack[0];
		stack := stack[1..];
		match t
		{
			case Tip(x) => io.Output(x);
			case Node(t1, t2) => stack := [t1, t2] + stack;
		}

		assert 0 <= ForestSize(stack) < V0; // the loop terminates
	}
}
