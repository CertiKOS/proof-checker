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
applysub BM (sub S Hd) Res :- applymany BM S Res.

%%%%%%%%%%%%%%%%%%%% Typing Rules for Substitutions %%%%%%%%%%%%%%%%%%%%
subhdof emptysub emptyctx.
subhdof idsub (vctx V) :- cvof V.

subof (sub S Shd) (ctx C Chd) :- 
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