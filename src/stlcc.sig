%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Definition of the contextual simply typed lambda calculus (STLC-c)
%%
%% Author:    Yuting Wang
%% Created:   Aug 14, 2019
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

sig stlcc.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Multiple bindings %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
kind bindmany   type -> type -> type.
type body       Body -> bindmany Variable Body.
type bind       (Variable -> bindmany Variable Body) -> bindmany Variable Body.

type applymany  bindmany A B -> list A -> B -> o.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Language constructs %%%%%%%%%%%%%%%%%%%%
kind ty, tm, mvar, pftm  type.
kind sub, subhd          type.
kind ctx, ctxhd, cvar    type.
kind cty, ctm, cpftm     type.

% Substitutions
type emptysub   subhd.   % The empty substitution
type idsub      subhd.   % The identity substitution for contex
type sub        list tm -> subhd -> sub.

type applysub   bindmany tm B -> sub -> B -> o.

% Types
type tprop, a   ty.
type arr        ty -> ty -> ty.

% Terms
type c          tm.
type abs        ty -> (tm -> tm) -> tm.
type app        tm -> tm -> tm.
type eq         tm -> tm -> tm.
type mvar       sub -> mvar -> tm.

% Proof Terms
type cp         pftm.
type refl       tm -> pftm.
type trans      pftm -> pftm -> pftm.
type symm       pftm -> pftm.
type congAbs    ty -> (tm -> pftm) -> pftm.
type congAppL, congAppR, congEqL, congEqR    pftm -> pftm.
type beta       ty -> (tm -> tm) -> tm -> pftm.
type conv       pftm -> pftm -> pftm.

% Contexts
type emptyctx   ctxhd.           % Empty context
type vctx       cvar -> ctxhd.   % Context head containing a variable
type ctx        list ty -> ctxhd -> ctx.

% Contextual types 
type cty        ctx -> bindmany tm ty -> cty.

% Contextual terms
type ctm        ctx -> bindmany tm tm -> ctm.

% Contextual proof terms
type cpftm      ctx -> bindmany tm pftm -> cpftm.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Predicate Symbols for Typing %%%%%%%%%%%%%%%%%%%%

type of         tm -> ty -> o.       % Type of terms
type oflist     list tm -> list ty -> o.
type pof        pftm -> tm -> o.     % Type of proof terms
type mvof       mvar -> cty -> o.    % Type of meta variables
type cvof       cvar -> o.           % Existence of context variables
type subof      sub -> ctx -> o.     % Type of substitutions
type subhdof    subhd -> ctxhd -> o. 


