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
		match t
		{
			case Tip(x) =>
			{
				assert s == [t] + stack;
				assert LoopInv(tree, s, io.omega, old(io.omega));
				// ==>?
				assert LoopInv(tree, stack, io.omega + [x], old(io.omega)); // maintaining the loop invariant
				io.Output(x);
				assert LoopInv(tree, stack, io.omega, old(io.omega)); // maintaining the loop invariant
			}
			case Node(t1, t2) =>
			{
				assert s == [t] + stack;
				assert LoopInv(tree, s, io.omega, old(io.omega));
				// ==>?
				assert LoopInv(tree, [t1, t2] + stack, io.omega, old(io.omega));
				stack := [t1, t2] + stack;
				assert LoopInv(tree, stack, io.omega, old(io.omega)); // maintaining the loop invariant
			}
		}

		assert LoopInv(tree, stack, io.omega, old(io.omega)); // maintaining the loop invariant
		assert 0 <= ForestSize(stack) < V0; // the loop terminates
	}

	assert LoopInv(tree, stack, io.omega, old(io.omega)); // from the loop invariant
	assert stack == []; // from the negation of the loop guard
	// ==>
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
