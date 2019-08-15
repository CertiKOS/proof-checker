%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Type system of the contextual simply typed lambda calculus (STLC-c)
%%
%% Author:    Yuting Wang
%% Created:   Aug 14, 2019
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
module stlcc.

%%%%%%%%%%%%%%%%%%%% Operations on bindings %%%%%%%%%%%%%%%%%%%% 
applymany (body B) [] B.
applymany (bind F) (X :: XS) B :- applymany (F X) CS B.

%%%%%%%%%%%%%%%%%%%%% Substitutions %%%%%%%%%%%%%%%%%%%%
applysub BM (sub Hd S) Res :- applymany BM S Res.

%%%%%%%%%%%%%%%%%%%% Typing Rules for Substitutions %%%%%%%%%%%%%%%%%%%%
subhdof emptysub emptyctx.
subhdof (idsub V) (vctx V) :- cvof V.

subof (sub Shd S) (ctx Chd C) :- 
  subhdof Shd Chd, oflist S C.

%%%%%%%%%%%%%%%%%%%% Typing Rules for Terms %%%%%%%%%%%%%%%%%%%%
of c a.
of (abs Ty1 R) (arr Ty1 Ty2) :-
   pi x\ of x Ty1 => of (R x) Ty2.
of (app Tm1 Tm2) Ty2 :- of Tm1 (arr Ty1 Ty2), of Tm2 Ty1.
of (eq Tm1 Tm2) tprop :- of Tm1 T, of Tm2 T.
of (mvar Sub X) Ty' :-
   mvof X (cty Ctx Ty), subof Sub Ctx, applysub Ty Sub Ty'.

oflist nil nil.
oflist (Tm :: Tml) (Ty :: Tyl) :- of Tm Ty, oflist Tml Tyl.

%%%%%%%%%%%%%%%%%%%% Typing Rules for Proof Terms %%%%%%%%%%%%%%%%%%%%
pof cp c.
pof (refl Pm) (eq Tm Tm):- of Tm Ty.
pof (trans Pm1 Pm2) (eq Tm1 Tm3) :-
  pof Pm1 (eq Tm1 Tm2), pof Pm2 (eq Tm2 Tm3).
pof (symm Pm) (eq Tm1 Tm2) :- pof Pm (eq Tm2 Tm1).
pof (congAbs Ty Pmr) (eq (abs Ty Tmr1) (abs Ty Tmr2)) :-
  pi x\ of x Ty => pof (Pmr x) (eq (Tmr1 x) (Tmr2 x)).
pof (congAppL Pm) (eq (app Tm1 Tm2) (app Tm1' Tm2)) :- 
  pof Pm (eq Tm1 Tm1'),
  of Tm1 (arr Ty1 Ty2), of Tm2 Ty1.
pof (congAppR Pm) (eq (app Tm1 Tm2) (app Tm1 Tm2')) :-
  pof Pm (eq Tm2 Tm2'),
  of Tm1 (arr Ty1 Ty2), of Tm2 Ty1.
pof (congEqL Pm) (eq (eq Tm1 Tm2) (eq Tm1' Tm2)) :-
  pof Pm (eq Tm1 Tm1'), of Tm1 Ty, of Tm2 Ty.
pof (congEqR Pm) (eq (eq Tm1 Tm2) (eq Tm1 Tm2')) :-
  pof Pm (eq Tm2 Tm2'), of Tm1 Ty, of Tm2 Ty.
pof (beta Ty1 Tmr1 Tm2) (eq (app (abs Ty1 Tmr1) Tm2) (Tmr1 Tm2)) :-
  of (abs Ty1 Tmr1) (arr Ty1 Ty2), of Tm2 Ty1.
pof (conv Pm1 Pm2) Tm2 :-
  pof Pm1 Tm1, pof Pm2 (eq Tm1 Tm2).

%%%%%%%%%%%%%%%%%%%% Typing Rules for Contextual Terms %%%%%%%%%%%%%%%%%%%%
cof (ctm Ctx Tm) (cty Ctx Ty) :-
  Ctx = ctx emptyctx C, 
  cofBind C Tm Ty.
cof (ctm Ctx Tm) (cty Ctx Ty) :-
  Ctx = ctx (vctx V) C, 
  (ctxv V => cofBind C Tm Ty).

cofBind nil (body Tm) (body Ty) :- of Tm Ty.
cofBind (Ty :: Tys) (bind Tmr) (bind Tyr) :-
  pi x\ of x Ty => cofBind Tys (Tmr x) (Tyr x).


%%%%%%%%%%%%%%%%%%%% Typing Rules for Contextual Proof Terms %%%%%%%%%%%%%%%
cpof (cpftm Ctx Pm) (ctm Ctx Tm) :-
  Ctx = ctx emptyctx C,
  cpofBind C Pm Tm.
cpofBind nil (body Pm) (body Tm) :- pof Pm Tm.
cpofBind (Ty :: Tys) (bind Pmr) (bind Tmr) :-
  pi x\ of x Ty => cpofBind Tys (Pmr x) (Tmr x).





