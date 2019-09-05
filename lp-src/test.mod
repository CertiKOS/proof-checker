%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Test cases for the contextual simply typed lambda calculus (STLC-c)
%%
%% Author:    Yuting Wang
%% Created:   Aug 14, 2019
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

module test.

accumulate stlcc.

%% X: [x:a -> a]a; y: a -> a |- X/[y] : a
metavar_tst1 T :-
  pi X\ mvof X (cty (ctx emptyctx (arr a a :: nil)) (bind (x\ body a))) =>
  pi y\ of y (arr a a) => 
  of (mvar (sub emptysub (y::nil)) X) T.

%% X: [x:a -> a](a -> a); y: a -> a |- (X/[y]) c : a
metavar_tst2 T :-
  pi X\ mvof X (cty (ctx emptyctx (arr a a :: nil)) (bind (x\ body (arr a a)))) =>
  pi y\ of y (arr a a) => 
  of (app (mvar (sub emptysub (y::nil)) X) c) T.

%% X: [x:a -> a](a -> a); y: a -> a |- (X/[z\ y z]) c : a
metavar_tst3 T :-
  pi X\ mvof X (cty (ctx emptyctx (arr a a :: nil)) (bind (x\ body (arr a a)))) =>
  pi y\ of y (arr a a) => 
  of (app (mvar (sub emptysub ((abs a (z\ app y z))::nil)) X) c) T.

%% z:a -> a |- (fun x:a->a => fun y:a => x y) z = (fun y:a => z y)
pof_tst1 Pm :-
  (Pm = z\ beta (Ty1 z) (Tmr1 z) (Tmr2 z)),
  (pi z\ of z (arr a a) => 
    pof (Pm z) (eq (app (abs (arr a a) x\ abs a y\ app x y) z) (abs a y\ app z y))).


pof_tst2 Pm :-
  (Pm = z\ trans (congAppL (beta (Ty1 z) (Tmr1 z) (Tmr2 z)))
                 (beta (Ty1' z) (Tmr1' z) (Tmr2' z))),
  pi z\ of z (arr a a) => 
    pof (Pm z) (eq (app (app (abs (arr a a) x\ abs a y\ app x y) z) c) (app z c)).

%% |- [x:a -> a, y: a] (x y) : [x:a -> a, y:a]a
cof_tst1 T :-
  cof (ctm (ctx emptyctx (arr a a::a::nil)) (bind x\ bind y\ body (app x y))) T.

