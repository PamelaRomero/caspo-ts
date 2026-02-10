#const maxsize = -1.
% #const maxrss = -1.

#program base.

%% data normalization

obsSpec(E,T,S) :- obs(E,T,S,X).
obsSpec(E,T,S) :- clamped(E,S,X), timepoint(E,T).
species(S) :- node(S,_).
unobsSpec(E,T,S) :- timepoint(E,T), species(S), not obsSpec(E,T,S).

measured(E,T,S,2) :- obs(E,T,S,X), X >= 60.
measured(E,T,S,1) :- obs(E,T,S,X), X < 60, X >= 30.
measured(E,T,S,0) :- obs(E,T,S,X), X < 30.

obsSpec(E,T,S) :- obs(E,T,S,X).
obsSpec(E,T,S) :- clamped(E,S,X), timepoint(E,T).

timepoint(E,T) :- measured(E,T,_,_).

maxtp(E,M) :- M = #max {T : timepoint(E,T)}, exp(E).
nextTP(E,T,T+1)    :- timepoint(E,T), timepoint(E,T+1).
nnextTP(E,T,T+1)   :- timepoint(E,T), not timepoint(E,T+1), T < M, maxtp(E,M).
nnextTP(E,T1,T2+1) :- nnextTP(E,T1,T2), not timepoint(E,T2+1).
nextTP(E,T1,T2+1)  :- nnextTP(E,T1,T2), timepoint(E,T2+1).

last(E,T) :- maxtp(E,T).

clause(X) :- clause(X,_,_).

toGuess(E,T,S) :- obs(E,T,S,X).
1{guessed(E,T,S,(2;1;0))}1  :- toGuess(E,T,S).
1{guessed(E,T,S,(2;1;0))}1  :- unobsSpec(E,T,S).
1{measured(E,T,S,(2;1;0))}1 :- unobsSpec(E,T,S).
%no errors in the unmeasured species
:-  unobsSpec(E,T,S), measured(E,T,S,V), not guessed(E,T,S,V).

%i have to have the same precondition (time 0) in all experiments
:- unobsSpec(E1,0,S), unobsSpec(E2,0,S), E1 < E2, measured(E1,0,S,V), not measured(E2,0,S,V).


%% support consistency

supp(E,T,L,V) :- guessed(E,T,L,V), nextTP(E,T,_).
convert(-1,0).
convert(1,1).
convert(2,2).
supp(E,T,L,V2) :- clamped(E,L,V1), convert(V1,V2), nextTP(E,T,_).

% We derive all values that we can potentially reach by a transition from the state u:

%ex_supp(E,T,clause,X,1) :- supp(E,T,L,C) : clause(X,L,V), convert(V,C); timepoint(E,T), clause(X).

ex_supp(E,T,clause,X,1) :- supp(E,T,L,C) : clause(X,L,V), convert(V,C), V != 2; timepoint(E,T), clause(X).   
ex_supp(E,T,clause,X,2) :- supp(E,T,L,C) : clause(X,L,V), convert(V,C), V = 2; timepoint(E,T), clause(X).   

%ex_supp(E,T,clause,X,1) :- supp(E,T,L,1) : clause(X,L,1), convert(1,1); timepoint(E,T), clause(X).
%ex_supp(E,T,clause,X,1) :- supp(E,T,L,0) : clause(X,L,-1), convert(-1,0); timepoint(E,T), clause(X).
%ex_supp(E,T,clause,X,2) :- supp(E,T,L,2) : clause(X,L,2), convert(2,2); timepoint(E,T), clause(X).

ex_supp(E,T,clause,X,0) :- supp(E,T,L,0), clause(X,L,1).
ex_supp(E,T,clause,X,0) :- supp(E,T,L,1), clause(X,L,-1).

ex_supp(E,T,clause,X,0) :- supp(E,T,L,0), clause(X,L,2).
ex_supp(E,T,clause,X,0) :- supp(E,T,L,2), clause(X,L,-1).

ex_supp(E,T,clause,X,0) :- supp(E,T,L,1), clause(X,L,2).
ex_supp(E,T,clause,X,0) :- supp(E,T,L,2), clause(X,L,1).


dnf(D) :- dnf(D,_).
ex_supp(E,T,dnf,X,1) :- ex_supp(E,T,clause,C,1), dnf(X,C).
ex_supp(E,T,dnf,X,2) :- ex_supp(E,T,clause,C,2), dnf(X,C).
ex_supp(E,T,dnf,X,0) :- ex_supp(E,T,clause,C,0) : dnf(X,C); dnf(X), nextTP(E,T,_).

opposite(0,1).
opposite(0,2).
opposite(1,0).
opposite(1,2).
opposite(2,0).
opposite(2,1).

clamped(E,S) :- clamped(E,S,V).

%if we do not have guessed the opposing thing, we can have external support

ex_supp(E,T,L,X) :- formula(L,D), ex_supp(E,T,dnf,D,X), not clamped(E,L), opposite(X,Y), not guessed(E,T2,L,Y), nextTP(E,T,T2).

% if we guessed the opposing thing, the opposing thing needs to be justified before we can give support

{ex_supp(E,T,L,X)} :- formula(L,D), ex_supp(E,T,dnf,D,X), not clamped(E,L), opposite(X,Y), guessed(E,T2,L,Y), nextTP(E,T,T2).

supp(E,T,L,X) :- ex_supp(E,T,L,X).

% The next state y belongs to the meta-state u (y ∈ u):
% The rule ensures that the state at time-point T + 1 is in the meta-state reachable from time-point T .

:- guessed(E,T2,S,V), not supp(E,T1,S,V), nextTP(E,T1,T2).

% If for some i, x_i = y_i and {0, 1} = u_i then there exists a transition f_i(z) = y_i:
% The rule implements the condition in the third item in the definition of support consistency described in the Formal Description section. It states
% that if a state at time-point T + 1 has value V and in the update predicate it has value W then there must exist an update in-between to recover the final value V .

:- guessed(E,T2,L,Y), opposite(X,Y), ex_supp(E,T1,L,X), not ex_supp(E,T1,L,Y), nextTP(E,T1,T2).


#program guess_bn.

% guess a formula compatible with the pkn for each node
formula(V,I)              :- node(V,I); hyper(I,_,_).
{dnf(I,J) : hyper(I,J,N)} :- formula(V,I).
clause(J,V,S)             :- edge(J,V,S); dnf(_,J).

% paths derived from the guess Boolean network
path(U,V) :- formula(V,I); dnf(I,J); edge(J,U,_).
path(U,V) :- path(U,W); path(W,V).

% J2 subsumed by J1
:- formula(V,I); hyper(I,J1,N); hyper(I,J2,M); N < M,
   dnf(I,J1);  dnf(I,J2); clause(J2,U,S) : clause(J1,U,S).

% contradictions
:- formula(V,I); dnf(I,J); edge(J,U,S); edge(J,U,-S).

% V is not leading to any readout (non-observable)
:- path(_,V); not readout(V); not path(V,U) : readout(U).

:- maxsize + 1 #sum {L,I,J : dnf(I,J) , hyper(I,J,L) }; maxsize >= 0.
%:- maxrss + 1 #sum {W,E,V,S : not eval(E,V,-S) , obs(E,V,D) , rss(D,V,S,W) }; maxrss >= 0.

#program guess_bn_controllable.

% V is not reached by any stimulus (non-controllable)
:- dnf(I,J); edge(J,V,_); not stimulus(V);
   not path(U,V) : stimulus(U).

#program diversity.

#heuristic dnf(I,J) : before(I,J). [2@2,false] %diversity
#heuristic dnf(I,J). [1,false] %subset
#external before(I,J)  : dnf(I,J). %diversity

#program block_solution.

:- dnf(I,J) : (I,J) = @dnf(). % no repeating of answer sets

#program minimize_size.

#minimize{L@1,I,J : dnf(I,J) , hyper(I,J,L)}.

#program fix_size(minSize, maxSize).

:- not minSize #sum {L,I,J : dnf(I,J) , hyper(I,J,L)} maxSize.

#program minimize_weight.

#minimize {Erg@2,E,T,S : measured(E,T,S,V), not guessed(E,T,S,V), toGuess(E,T,S), obs(E,T,S,M), Erg=30-M, M < 30}.
#minimize {Erg@2,E,T,S : measured(E,T,S,V), not guessed(E,T,S,V), toGuess(E,T,S), obs(E,T,S,M), Erg=|M-45|, M >= 30, M < 60}.
#minimize {Erg@2,E,T,S : measured(E,T,S,V), not guessed(E,T,S,V), toGuess(E,T,S), obs(E,T,S,M), Erg=M-59, M >= 60}.

#program fix_weight(minWeight, maxWeight).
:- not minWeight #sum {Erg,E,T,S : measured(E,T,S,V), not guessed(E,T,S,V), toGuess(E,T,S), obs(E,T,S,M), Erg=30-M, M < 30;
                       Erg,E,T,S : measured(E,T,S,V), not guessed(E,T,S,V), toGuess(E,T,S), obs(E,T,S,M), Erg=|M-45|, M >= 30, M < 60;
                       Erg,E,T,S : measured(E,T,S,V), not guessed(E,T,S,V), toGuess(E,T,S), obs(E,T,S,M), Erg=M-59, M >= 60} maxWeight.


#show formula/2.
#show dnf/2.
#show clause/3.
