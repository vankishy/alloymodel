module modules/TicTacToe

open util/ordering[GameState]

abstract sig Player {}
one sig Empty extends Player{}
abstract sig Symbol extends Player{}
one sig X extends Symbol{}
one sig O extends Symbol{}

sig GameState {
	turn: Symbol,
	sq1: Player,
	sq2: Player,
	sq3: Player,
	sq4: Player,
	sq5: Player,
	sq6: Player,
	sq7: Player,
	sq8: Player,
	sq9: Player
}

pred Win[s: GameState, t: Player] {
	t in Symbol and
		s.sq1 = t and s.sq2 = t and s.sq3 = t // row 1
		or s.sq4 = t and s.sq5 = t and s.sq6 = t // row 2
		or s.sq7 = t and s.sq8 = t and s.sq9 = t // row 3
		or s.sq1 = t and s.sq4 = t and s.sq7 = t // col 1
		or s.sq2 = t and s.sq5 = t and s.sq8 = t // col 2
		or s.sq3 = t and s.sq6 = t and s.sq9 = t // col 3
		or s.sq1 = t and s.sq5 = t and s.sq9 = t //diag 1
		or s.sq3 = t and s.sq5 = t and s.sq7 = t // diag 2
}

pred Draw[s: GameState] {
	not Win[s, X]
	and not Win[s, O]
	and s.sq1 in Symbol
	and s.sq2 in Symbol
	and s.sq3 in Symbol
	and s.sq4 in Symbol
	and s.sq5 in Symbol
	and s.sq6 in Symbol
	and s.sq7 in Symbol
	and s.sq8 in Symbol
	and s.sq9 in Symbol
}

pred Init[s: GameState, t: Symbol] {
	s.sq1 = Empty and
	s.sq2 = Empty and 
	s.sq3 = Empty and
	s.sq4 = Empty and
	s.sq5 = Empty and
	s.sq6 = Empty and
	s.sq7 = Empty and
	s.sq8 = Empty and
	s.sq9 = Empty and
	s.turn = t
}

pred Transition[s, s1: GameState]{
	s1.turn = NextTurn[s]

	not (Win[s, X] or Win[s, O] or Draw[s]) =>
		NextTurn[s] = O => CheckSymbols[s, s1, O]
			else NextTurn[s] = X => CheckSymbols[s, s1, X]

	s.sq1 = X => s1.sq1 = X 
	 s.sq1 = O => s1.sq1 = O
	s.sq2 = X => s1.sq2 = X 
	 s.sq2 = O => s1.sq2 = O
	s.sq3 = X => s1.sq3 = X 
	 s.sq3 = O => s1.sq3 = O
	s.sq4 = X => s1.sq4 = X 
	 s.sq4 = O => s1.sq4 = O
	s.sq5 = X => s1.sq5 = X 
	 s.sq5 = O => s1.sq5 = O
	s.sq6 = X => s1.sq6 = X 
	 s.sq6 = O => s1.sq6 = O
	s.sq7 = X => s1.sq7 = X 
	 s.sq7 = O => s1.sq7 = O
	s.sq8 = X => s1.sq8 = X 
	 s.sq8 = O => s1.sq8 = O
	s.sq9 = X => s1.sq9 = X 
	 s.sq9 = O => s1.sq9 = O

	((#(s.sq1 & Empty)) fun/add (#(s.sq2 & Empty)) fun/add (#(s.sq3 & Empty)) fun/add (#(s.sq4 & Empty))
		fun/add (#(s.sq5 & Empty)) fun/add (#(s.sq6 & Empty)) fun/add (#(s.sq7 & Empty)) fun/add (#(s.sq8 & Empty))
		fun/add (#(s.sq9 & Empty)).minus[1]
			=   (#(s1.sq1 & Empty)) fun/add (#(s1.sq2 & Empty)) fun/add (#(s1.sq3 & Empty)) fun/add (#(s1.sq4 & Empty))
				fun/add (#(s1.sq5 & Empty)) fun/add (#(s1.sq6 & Empty)) fun/add (#(s1.sq7 & Empty)) fun/add (#(s1.sq8 & Empty))
				fun/add (#(s1.sq9 & Empty)))
}

fun NextTurn[s: GameState]:Symbol {
	{m: Symbol| m not in s.turn}
}

// checks to make sure  1 more x or o was added
pred CheckSymbols[s, s1: GameState, sym: Symbol]{
	s1.turn = sym => (#(s.sq1 & sym)) fun/add (#(s.sq2 & sym)) fun/add (#(s.sq3 & sym)) fun/add (#(s.sq4 & sym))
		fun/add (#(s.sq5 & sym)) fun/add (#(s.sq6 & sym)) fun/add (#(s.sq7 & sym)) fun/add (#(s.sq8 & sym))
		fun/add (#(s.sq9 & sym)) fun/add 1
			=   (#(s1.sq1 & sym)) fun/add (#(s1.sq2 & sym)) fun/add (#(s1.sq3 & sym)) fun/add (#(s1.sq4 & sym))
				fun/add (#(s1.sq5 & sym)) fun/add (#(s1.sq6 & sym)) fun/add (#(s1.sq7 & sym)) fun/add (#(s1.sq8 & sym))
				fun/add (#(s1.sq9 & sym))
}


pred Trace {
	first.Init[O]
	all s: GameState-last |
		let s1 = s.next |
			Transition[s, s1]
}

pred WinTrace {
	first.Init[O]
	all s: GameState-last |
		let s1 = s.next |
			Transition[s, s1] and not Draw[s]
	Win[last, X] or Win[last, O]
}


pred DrawTrace {
	first.Init[O]
	all s: GameState-last |
		let s1 = s.next |
			Transition[s, s1] and not (Win[s, O] or Win[s, X])
	Draw[last]
}

run DrawTrace for 10 but 5 Int
