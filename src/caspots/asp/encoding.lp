#const maxsize = -1.
% #const maxrss = -1.


#program base.

%% Sata normalization

obsSpec(E,T,S) :- obs(E,T,S,X).
obsSpec(E,T,S) :- clamped(E,S,X), timepoint(E,T).
species(S) :- node(S,_).
unobsSpec(E,T,S) :- timepoint(E,T), species(S), not obsSpec(E,T,S).

% Now we include the value 2 and we have two thresholds at 30 and 60
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

% We consider the value 2 for the guessed data.
1{guessed(E,T,S,(2;1;0))}1  :- toGuess(E,T,S).
1{guessed(E,T,S,(2;1;0))}1  :- unobsSpec(E,T,S).
1{measured(E,T,S,(2;1;0))}1 :- unobsSpec(E,T,S).

%no errors in the unmeasured species
:-  unobsSpec(E,T,S), measured(E,T,S,V), not guessed(E,T,S,V).

%i have to have the same precondition (time 0) in all experiments
:- unobsSpec(E1,0,S), unobsSpec(E2,0,S), E1 < E2, measured(E1,0,S,V), not measured(E2,0,S,V).

%% Support consistency

meta(E,T,L,V) :- guessed(E,T,L,V), nextTP(E,T,_).

% We maintained that the clause takes a value equal to the sign of the edge (-1 or 1), and allowed for the possibility that the 1 could be either a 1 or a 2.
convert(-1,0).
convert(1,1).
convert(1,2).

% If the edge sign is not -1, the meta-state value will match the clamped value (1 or 2); if the sign value is -1, the meta-state will have a value of 0.
meta(E,T,L,V) :- clamped(E,L,V), V != -1, nextTP(E,T,_).
meta(E,T,L,V2) :- clamped(E,L,V1), V1 = -1, convert(V1,V2), nextTP(E,T,_).

% Clause update

% We check whether the arguments are valid, this means if the value of the clause matches the value of the meta-state within the same argument, if it is valid, it will retain its value.
arg_valid(E,T,X,L,C) :- meta(E,T,L,C), clause(X,L,V), convert(V,C), timepoint(E,T), clause(X).

% If the values ​​are not valid, the argument will have a value of zero. It is invalid when the clause value is -1 and the meta-state is 1 or 2, or if the clause value is 1 and the meta-state is 0.
arg_no_valid(E,T,X,L,0) :- meta(E,T,L,1), clause(X,L,-1), timepoint(E,T), clause(X).
arg_no_valid(E,T,X,L,0) :- meta(E,T,L,2), clause(X,L,-1), timepoint(E,T), clause(X).
arg_no_valid(E,T,X,L,0) :- meta(E,T,L,0), clause(X,L,1), timepoint(E,T), clause(X).

% We count how many valid arguments there are per clause.
count_arg_valid_clause(E,T,X,V) :- V = #count{L : arg_valid(E,T,X,L,W)}, timepoint(E,T), clause(X).

% We count the number of arguments per clause.
count_arg_clause(X,V) :- V = #count{L : clause(X,L,W)}, clause(X).

% We calculate the maximum value among all valid arguments associated with the same clause.
maxi(E,T,X,V) :- V = #max{W : arg_valid(E,T,X,L,W)}, timepoint(E,T), clause(X).

% We update the clause value to 0 when there is an invalid argument within the clause.
update(E,T,clause,X,0) :- arg_no_valid(E,T,X,L,0).
% We update the clause value to 0 when the number of arguments per clause does not match the number of valid arguments per clause.
update(E,T,clause,X,0) :- count_arg_clause(X,V3), count_arg_valid_clause(E,T,X,V4), V3 != V4.
% We update the clause value to 1 when the number of arguments per clause matches the number of valid arguments per clause, and the maximum value of the clause's valid arguments is not 2.
update(E,T,clause,X,1) :- maxi(E,T,X,V1), V1 != 2, count_arg_clause(X,V3), count_arg_valid_clause(E,T,X,V4), V3 = V4. 
% We update the clause value to 1 when the number of arguments per clause matches the number of valid arguments per clause, and we have a value of 1 for valid arguments. 
update(E,T,clause,X,1) :- arg_valid(E,T,X,L,1), count_arg_clause(X,V3), count_arg_valid_clause(E,T,X,V4), V3 = V4. 
% We update the clause value to 2 when the number of arguments per clause matches the number of valid arguments per clause, and the maximum value of the clause's valid arguments is 2.
update(E,T,clause,X,2) :- maxi(E,T,X,V1), V1 = 2, count_arg_clause(X,V3), count_arg_valid_clause(E,T,X,V4), V3 = V4. 

dnf(D) :- dnf(D,_).

% We update the dnf value to 2 when there is an update of the clause equal to 2.
update(E,T,dnf,X,2) :- update(E,T,clause,C,2), dnf(X,C). 
% We update the dnf value to 0 when there is all updates of the clause are equal to 0.
update(E,T,dnf,X,0) :- update(E,T,clause,C,0) : dnf(X,C); dnf(X), nextTP(E,T,_).   
% We update the dnf value to 1 when there is all updates of the clause are equal to 1.
update(E,T,dnf,X,1) :- update(E,T,clause,C,1) : dnf(X,C); dnf(X), nextTP(E,T,_).   
% We update the dnf value to 1 when there are clause updates equal to 0 and 1.
update(E,T,dnf,X,1) :- update(E,T,clause,C1,0), update(E,T,clause,C2,1), dnf(X,C1), dnf(X,C2).   

% We add opposite values
opposite(0,2).  
opposite(2,0). 
opposite(1,0).
opposite(0,1).


clamped(E,S) :- clamped(E,S,V).
% If we do not have guessed the opposing thing, we can have external support
update(E,T,L,X) :- formula(L,D), update(E,T,dnf,D,X), not clamped(E,L), opposite(X,Y), not guessed(E,T2,L,Y), nextTP(E,T,T2).  
% If we guessed the opposing thing, the opposing thing needs to be justified before we can give support
{update(E,T,L,X)} :- formula(L,D), update(E,T,dnf,D,X), not clamped(E,L), opposite(X,Y), guessed(E,T2,L,Y), nextTP(E,T,T2). 

meta(E,T,L,X) :- update(E,T,L,X).

:- guessed(E,T2,S,V), not meta(E,T1,S,V), nextTP(E,T1,T2).

:- guessed(E,T2,L,Y), opposite(X,Y), update(E,T1,L,X), not update(E,T1,L,Y), nextTP(E,T1,T2).


#program guess_bn.
%#program base.

% guess a formula compatible with the pkn for each node
formula(V,I)              :- node(V,I); hyper(I,_,_).
{dnf(I,J) : hyper(I,J,N)} :- formula(V,I).
clause(J,V,S)             :- edge(J,V,S); dnf(_,J).
clause(J,V,2)             :- edge(J,V,S); dnf(_,J). 

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


% Here, we consider a penalty when the guessed and the measured data have different values.

%#program minimize_weight.
%#minimize {Erg@2,E,T,S : measured(E,T,S,V), guessed(E,T,S,W), toGuess(E,T,S), Erg=0, V=W}.
%#minimize {Erg@2,E,T,S : measured(E,T,S,V), guessed(E,T,S,W), toGuess(E,T,S), Erg=V-W, W < V}.
%#minimize {Erg@2,E,T,S : measured(E,T,S,V), guessed(E,T,S,W), toGuess(E,T,S), Erg=W-V, V < W}.

%#program fix_weight(minWeight, maxWeight).
%:- #sum {Erg,E,T,S : measured(E,T,S,V), not guessed(E,T,S,V), guessed(E,T,S,W), toGuess(E,T,S), obs(E,T,S,M), Erg=0, V=W;
%         Erg,E,T,S : measured(E,T,S,V), not guessed(E,T,S,V), guessed(E,T,S,W), toGuess(E,T,S), obs(E,T,S,M), Erg=V-W, W < V;
%         Erg,E,T,S : measured(E,T,S,V), not guessed(E,T,S,V), guessed(E,T,S,W), toGuess(E,T,S), obs(E,T,S,M), Erg=W-V, V < W} > maxWeight.                   


% Here, we consider the penalty based on the distance to the thresholds of 30 and 60; we divide the interval between 30 and 60 into two sections, with the aim of approaching the corresponding threshold in each section.

#program minimize_weight.

#minimize {Erg@2,E,T,S : measured(E,T,S,V), not guessed(E,T,S,V), toGuess(E,T,S), obs(E,T,S,M), Erg=30-M, M < 30}.
#minimize {Erg@2,E,T,S : measured(E,T,S,V), not guessed(E,T,S,V), toGuess(E,T,S), obs(E,T,S,M), Erg=M-59, M >= 60}.
#minimize {Erg@2,E,T,S : measured(E,T,S,V), not guessed(E,T,S,V), toGuess(E,T,S), obs(E,T,S,M), Erg=M-29, M >= 30, M < 45}.
#minimize {Erg@2,E,T,S : measured(E,T,S,V), not guessed(E,T,S,V), toGuess(E,T,S), obs(E,T,S,M), Erg=60-M, M >= 45, M < 60}.

#program fix_weight(minWeight, maxWeight).
:- not minWeight #sum {Erg,E,T,S : measured(E,T,S,V), not guessed(E,T,S,V), toGuess(E,T,S), obs(E,T,S,M), Erg=30-M, M < 30;
                       Erg,E,T,S : measured(E,T,S,V), not guessed(E,T,S,V), toGuess(E,T,S), obs(E,T,S,M), Erg=M-29, M >= 30, M < 45;
                       Erg,E,T,S : measured(E,T,S,V), not guessed(E,T,S,V), toGuess(E,T,S), obs(E,T,S,M), Erg=60-M, M >= 45, M < 60;
                       Erg,E,T,S : measured(E,T,S,V), not guessed(E,T,S,V), toGuess(E,T,S), obs(E,T,S,M), Erg=M-59, M >= 60} maxWeight.





%#show update/5.
%#show update/4.
%#show meta/4.
%#show guessed/4.
%#show measured/4.
%#show toGuess/3.

%#show formula/2.
%#show dnf/2.
%#show clause/3.
%#show hyper/3. 
%#show path/2.
%#show edge/3.
%#show readout/1.

%#show obsSpec/3.
%#show species/1.
%#show unobsSpec/3.
%#show measured/4.
%#show timepoint/2.
%#show maxtp/2.
%#show nextTP/3.
%#show nnextTP/3.
%#show last/2.
%#show clause/1.

%#show clamped/3.
%#show mini/4.
%#show maxi/4.
%#show diff/4.
