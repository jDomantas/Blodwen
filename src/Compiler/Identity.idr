module Compiler.Scheme.Chicken

import Compiler.Common
import Compiler.CompileExpr
import Compiler.Inline

import Core.Context
import Core.Directory
import Core.Name
import Core.Options
import Core.TT

import Data.CMap
import Data.List
import Data.Vect
import System
import System.Info

%default covering


showNamePart : String -> String
showNamePart s = concatMap okchar (unpack s)
    where
        okchar : Char -> String
        okchar c =
            if isAlphaNum c || c =='_'
                then cast c
                else "C-" ++ show (cast {to=Int} c)

mutual
    schName : Name -> String
    schName (UN n) = showNamePart n
    schName (MN n i) = showNamePart n ++ "-" ++ show i
    schName (NS ns n) = showSep "-" ns ++ "-" ++ schName n
    schName (HN n i) = showNamePart n ++ "--" ++ show i
    schName (PV n d) = "pat--" ++ schName n
    schName (DN _ n) = schName n
    schName (GN g) = schGName g

    schGName : GenName -> String
    schGName (Nested o i) = schName i ++ "--in--" ++ schName o
    schGName (CaseBlock n i) = "case--" ++ schName n ++ "-" ++ show i
    schGName (WithBlock n i) = "with--" ++ schName n ++ "-" ++ show i

-- local variable names as scheme names - we need to invent new names for the locals
-- because there might be shadows in the original expression which can't be resolved
-- by the same scoping rules. (e.g. something that computes \x, x => x + x where the
-- names are the same but refer to different bindings in the scope)
public export
data SVars : List Name -> Type where
    Nil : SVars []
    (::) : (svar : String) -> SVars ns -> SVars (n :: ns)

extendSVars : (xs : List Name) -> SVars ns -> SVars (xs ++ ns)
extendSVars {ns} xs vs = extSVars' (cast (length ns)) xs vs
    where 
        extSVars' : Int -> (xs : List Name) -> SVars ns -> SVars (xs ++ ns)
        extSVars' i [] vs = vs
        extSVars' i (x :: xs) vs = schName (MN "v" i) :: extSVars' (i + 1) xs vs

initSVars : (xs : List Name) -> SVars xs
initSVars xs = rewrite sym (appendNilRightNeutral xs) in extendSVars xs []

lookupSVar : Elem x xs -> SVars xs -> String
lookupSVar Here (n :: ns) = n
lookupSVar (There p) (n :: ns) = lookupSVar p ns

schConstructor : Int -> List String -> String
schConstructor t args = "(make-object " ++ show t ++ " " ++ showSep " " args ++ ")"

call : String -> List String -> String
call o args = "(call" ++ o ++ " " ++ showSep " " args ++ ")"

op : String -> List String -> String
op o args = "(" ++ o ++ " " ++ showSep " " args ++ ")"

schOp : PrimFn arity -> Vect arity String -> String
schOp (Add ty) [x, y] = op "+" [x, y]
schOp (Sub ty) [x, y] = op "-" [x, y]
schOp (Mul ty) [x, y] = op "*" [x, y]
schOp (Div ty) [x, y] = op "/" [x, y]
schOp (Mod ty) [x, y] = op "mod" [x, y]
schOp (Neg ty) [x] = op "negate" [x]
schOp (LT ty) [x, y] = op "<" [x, y]
schOp (LTE ty) [x, y] = op "<=" [x, y]
schOp (EQ ty) [x, y] = op "=" [x, y]
schOp (GTE ty) [x, y] = op ">=" [x, y]
schOp (GT ty) [x, y] = op ">" [x, y]
schOp StrLength [x] = op "string-length" [x]
schOp StrHead [x] = op "string-head" [x]
schOp StrTail [x] = op "string-tail" [x]
schOp StrIndex [x, i] = op "string-get" [x, i]
schOp StrCons [x, y] = op "string-cons" [x, y]
schOp StrAppend [x, y] = op "string-append" [x, y]
schOp StrReverse [x] = op "string-reverse" [x]
schOp StrSubstr [x, y, z] = op "string-substr" [x, y, z]
schOp (Cast from to) [x] = op "cast" [show from, show to, x]
schOp BelieveMe [_, _, x] = x

schConstant : Constant -> String
schConstant (I x) = show x
schConstant (BI x) = show x
schConstant (Str x) = show x
schConstant (Ch x) = "\'" ++ cast x ++ "\'"
schConstant (Db x) = show x
schConstant WorldVal = "world"
schConstant IntType = "ty-int"
schConstant IntegerType = "ty-integer"
schConstant StringType = "ty-string"
schConstant CharType = "ty-char"
schConstant DoubleType = "ty-double"
schConstant WorldType = "ty-world"

schCaseDef : Maybe String -> String
schCaseDef Nothing = ""
schCaseDef (Just tm) = " (otherwise " ++ tm ++ ")"

mutual
    schConAlt : SVars vars -> CConAlt vars -> Core annot String
    schConAlt {vars} vs (MkConAlt n tag args sc)
        = let vs' = extendSVars args vs in
              pure $ "((" ++ show tag ++ bindArgs args vs' !(schExp vs' sc) ++ ")"
      where
        bindArgs : (ns : List Name) -> SVars (ns ++ vars) -> String -> String
        bindArgs [] v body = ")" ++ body
        bindArgs (n :: ns) (v :: vs) body = " " ++ v ++ bindArgs ns vs body

    schConstAlt : SVars vars -> CConstAlt vars -> Core annot String
    schConstAlt vs (MkConstAlt c exp)
        = pure $ "(" ++ schConstant c ++ !(schExp vs exp) ++ ")"
      
    -- oops, no traverse for Vect in Core
    schArgs : SVars vars -> Vect n (CExp vars) -> Core annot (Vect n String)
    schArgs vs [] = pure []
    schArgs vs (arg :: args) = pure $ !(schExp vs arg) :: !(schArgs vs args)

    export
    schExp : SVars vars -> CExp vars -> Core annot String
    schExp vs (CLocal el) = pure $ lookupSVar el vs
    schExp vs (CRef n) = pure $ schName n
    schExp vs (CLam x sc) 
       = do let vs' = extendSVars [x] vs 
            sc' <- schExp vs' sc
            pure $ "(lambda " ++ lookupSVar Here vs' ++ " " ++ sc' ++ ")"
    schExp vs (CLet x val sc) 
       = do let vs' = extendSVars [x] vs
            val' <- schExp vs val
            sc' <- schExp vs' sc
            pure $ "(let " ++ lookupSVar Here vs' ++ " " ++ val' ++ " " ++ sc' ++ ")"
    schExp vs (CApp x args) = pure $ call !(schExp vs x) !(traverse (schExp vs) args)
    schExp vs (CCon x tag args) = pure $ schConstructor tag !(traverse (schExp vs) args)
    schExp vs (COp op args) = pure $ schOp op !(schArgs vs args)
    schExp vs (CExtPrim p args) = throw $ InternalError "can't compile call to external primitive"
    schExp vs (CForce t) = pure $ op "force" [!(schExp vs t)]
    schExp vs (CDelay t) = pure $ op "delay" [!(schExp vs t)]
    schExp vs (CConCase sc alts def) 
        = do tcode <- schExp vs sc
             default <- maybe (pure Nothing) (\v => pure (Just !(schExp vs v))) def
             pure $ "(case " ++ tcode ++ " "
                     ++ showSep " " !(traverse (schConAlt vs) alts)
                     ++ schCaseDef default ++ ")"
    schExp vs (CConstCase sc alts def) 
        = do tcode <- schExp vs sc
             default <- maybe (pure Nothing) (\v => pure (Just !(schExp vs v))) def
             pure $ "(case-const " ++ tcode ++ " ("
                      ++ showSep " " !(traverse (schConstAlt vs) alts)
                      ++ schCaseDef default ++ ")"
    schExp vs (CPrimVal c) = pure $ schConstant c
    schExp vs CErased = pure "erased"
    schExp vs (CCrash msg) = pure $ "(error " ++ show msg ++ ")"

    argList : SVars ns -> String
    argList [] = ""
    argList [x] = x
    argList (x :: xs) = x ++ " " ++ argList xs

    schDef : Name -> CDef -> Core annot String
    schDef n (MkFun args exp) =
        let vs = initSVars args in
        pure $ "(function " ++ schName n ++ " (" ++ argList vs ++ ") " ++ !(schExp vs exp) ++ ")\n"
    schDef n (MkError exp)
        = pure $ "(function " ++ schName n ++ " (...) " ++ !(schExp [] exp) ++ ")\n"
    schDef n (MkCon t a) = pure ""
  
-- Convert the name to scheme code
-- (There may be no code generated, for example if it's a constructor)
export
getRepr : Defs -> Name -> Core annot String
getRepr defs n = case lookupGlobalExact n (gamma defs) of
    Nothing =>
        throw $ InternalError ("undefined name: " ++ show n)
    Just d =>
        case compexpr d of
            Nothing =>
                throw $ InternalError ("no compiled definition for " ++ show n)
            Just d =>
                schDef n d

compileTerm : Ref Ctxt Defs -> ClosedTerm -> (outfile : String) -> Core annot ()
compileTerm c tm outfile = do
    ds <- getDirectives Identity
    (ns, tags) <- findUsedNames tm
    defs <- get Ctxt
    compdefs <- traverse (getRepr defs) ns
    let code = concat compdefs
    main <- schExp [] !(compileExp tags tm)
    let repr = code ++ main
    Right () <- coreLift $ writeFile outfile repr
    | Left err => throw (FileErr outfile err)
    pure ()

compileExpr : Ref Ctxt Defs -> ClosedTerm -> (outfile : String) -> Core annot (Maybe String)
compileExpr c tm outfile = do
    compileTerm c tm outfile
    pure (Just outfile)

executeExpr : Ref Ctxt Defs -> ClosedTerm -> Core annot ()
executeExpr c tm = do pure ()

export
codegenIdentity : Codegen annot
codegenIdentity = MkCG compileExpr executeExpr

