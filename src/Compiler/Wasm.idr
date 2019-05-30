module Compiler.Wasm

import Compiler.Common
import Compiler.CompileExpr
import Compiler.Inline

import Core.Core
import Core.Context
import Core.TT

import Data.CMap
import Data.CSet
import Data.Vect
import Data.List

import Codegen
import TSExp
import TSExpToMir
import Trans
import Mir

wasmOp : Core.TT.PrimFn arity -> Vect arity (TSExp vars) -> Core annot (TSExp vars)
wasmOp (Add IntType) [x, y] = pure (Op Add [x, y])
wasmOp (Sub IntType) [x, y] = pure (Op Sub [x, y])
wasmOp (Mul IntType) [x, y] = pure (Op Mul [x, y])
wasmOp (Div IntType) [x, y] = pure (Op Div [x, y])
wasmOp (Mod IntType) [x, y] = pure (Op Mod [x, y])
wasmOp (Neg IntType) [x] = pure (Op Neg [x])
wasmOp (LT IntType) [x, y] = pure (Op LT [x, y])
wasmOp (LTE IntType) [x, y] = pure (Op LTE [x, y])
wasmOp (EQ IntType) [x, y] = pure (Op EQ [x, y])
wasmOp (GT IntType) [x, y] = pure (Op GT [x, y])
wasmOp (GTE IntType) [x, y] = pure (Op GTE [x, y])
wasmOp (Add IntegerType) [x, y] = pure (Op Add [x, y])
wasmOp (Sub IntegerType) [x, y] = pure (Op Sub [x, y])
wasmOp (Mul IntegerType) [x, y] = pure (Op Mul [x, y])
wasmOp (Div IntegerType) [x, y] = pure (Op Div [x, y])
wasmOp (Mod IntegerType) [x, y] = pure (Op Mod [x, y])
wasmOp (Neg IntegerType) [x] = pure (Op Neg [x])
wasmOp (LT IntegerType) [x, y] = pure (Op LT [x, y])
wasmOp (LTE IntegerType) [x, y] = pure (Op LTE [x, y])
wasmOp (EQ IntegerType) [x, y] = pure (Op EQ [x, y])
wasmOp (GT IntegerType) [x, y] = pure (Op GT [x, y])
wasmOp (GTE IntegerType) [x, y] = pure (Op GTE [x, y])
wasmOp BelieveMe [_,_,x] = pure x
wasmOp _ _ = throw (InternalError "unsupported primitive op")

wasmConstant : Constant -> Core annot TSConst
wasmConstant (I x) = pure (I (cast x))
wasmConstant (BI x) = pure (I x)
wasmConstant (Str x) = throw (InternalError "strings are not supported")
wasmConstant (Ch x) = throw (InternalError "characters are not supported")
wasmConstant (Db x) = throw (InternalError "doubles are not supported")
wasmConstant WorldVal = pure WorldVal
wasmConstant IntType = pure IntegerType
wasmConstant IntegerType = pure IntegerType
wasmConstant StringType = throw (InternalError "string types are not supported")
wasmConstant CharType = throw (InternalError "character types are not supported")
wasmConstant DoubleType = throw (InternalError "double types are not supported")
wasmConstant WorldType = pure WorldType

wasmConstantTag : Constant -> Core annot Int
wasmConstantTag (I x) = pure x
wasmConstantTag (BI x) = pure (fromInteger x)
wasmConstantTag (Str x) = throw (InternalError "strings are not supported")
wasmConstantTag (Ch x) = throw (InternalError "characters are not supported")
wasmConstantTag (Db x) = throw (InternalError "doubles are not supported")
wasmConstantTag WorldVal = pure 0
wasmConstantTag IntType = pure 0
wasmConstantTag IntegerType = pure 0
wasmConstantTag StringType = throw (InternalError "string types are not supported")
wasmConstantTag CharType = throw (InternalError "character types are not supported")
wasmConstantTag DoubleType = throw (InternalError "double types are not supported")
wasmConstantTag WorldType = pure 0

elemToFin : Data.List.Elem x xs -> Fin (length xs)
elemToFin Here = FZ
elemToFin (There x) = FS (elemToFin x)

lengthSum : (a : List x) -> (b : List x) -> (length a + length b = length (a ++ b))
lengthSum [] b = Refl
lengthSum (x :: xs) b = rewrite lengthSum xs b in Refl

lookupGlobal : (names : List Name) -> Name -> Maybe Nat
lookupGlobal [] name = Nothing
lookupGlobal (x :: xs) name =
    if x == name then
        Just Z
    else
        map S (lookupGlobal xs name)

showNames : List Name -> String
showNames [] = ""
showNames [x] = show x
showNames (x :: xs) = show x ++ "\n" ++ showNames xs

parameters (names : List Name)
    mutual
        traverseVect : Vect n (CExp vars) -> Core annot (Vect n (TSExp (length vars)))
        traverseVect [] = pure []
        traverseVect (x :: xs) = pure (!(wasmExp x) :: !(traverseVect xs))

        traverseMaybe : Maybe (CExp vars) -> Core annot (Maybe (TSExp (length vars)))
        traverseMaybe Nothing = pure Nothing
        traverseMaybe (Just x) = pure (Just !(wasmExp x))

        wasmBranch : {vars : List Name} -> CConAlt vars -> Core annot (Branch (length vars))
        wasmBranch {vars} (MkConAlt _ tag args exp) = do
            exp <- wasmExp exp
            pure (MkBranch tag (length args) (rewrite lengthSum args vars in exp))

        wasmConstBranch : CConstAlt vars -> Core annot (ConstBranch (length vars))
        wasmConstBranch (MkConstAlt c exp) = pure (MkConstBranch !(wasmConstantTag c) !(wasmExp exp))

        wasmExp : CExp vars -> Core annot (TSExp (length vars))
        wasmExp (CLocal el) = pure (Local (elemToFin el))
        wasmExp (CRef name) = case lookupGlobal names name of
            Just idx => pure (Global idx)
            Nothing => throw (InternalError ("undefined global: " ++ show name ++ "\ndefined globals:\n" ++ showNames names))
        wasmExp (CLam param body) = pure (Lam !(wasmExp body))
        wasmExp (CLet name val rest) = pure (Let !(wasmExp val) !(wasmExp rest))
        wasmExp (CApp f args) = pure (Apply !(wasmExp f) !(traverse wasmExp args))
        wasmExp (CCon name tag fields) = pure (Construct tag !(traverse wasmExp fields))
        wasmExp (COp op args) = wasmOp op !(traverseVect args)
        wasmExp (CExtPrim _ _) = throw (InternalError "external primitives are not supported")
        wasmExp (CForce e) = pure (Force !(wasmExp e))
        wasmExp (CDelay e) = pure (TSExp.Delay !(wasmExp e))
        wasmExp (CConCase sc alts def) = do
            sc <- wasmExp sc
            alts <- traverse wasmBranch alts
            def <- traverseMaybe def
            pure (Case sc alts def)
        wasmExp (CConstCase sc alts def) = do
            sc <- wasmExp sc
            alts <- traverse wasmConstBranch alts
            def <- traverseMaybe def
            pure (ConstCase sc alts def)
        wasmExp (CPrimVal c) = pure (Const !(wasmConstant c))
        wasmExp CErased = pure Erased
        wasmExp (CCrash msg) = pure (Crash msg)

        wasmDef : Name -> CDef -> Core annot TSDef
        wasmDef n (MkFun args exp) = pure (Function (length args) !(wasmExp exp))
        wasmDef n (MkError exp) = throw (InternalError "code contains error def")
        wasmDef n (MkCon t a) = pure (Constructor t a)

getWasmDef : (globals : List Name) -> Defs -> Name -> Core annot (Name, TSDef)
getWasmDef globals defs n = case lookupGlobalExact n (gamma defs) of
    Nothing => throw (InternalError ("Compiling undefined name " ++ show n))
    Just d => case compexpr d of
        Nothing => throw (InternalError ("No compiled definition for " ++ show n))
        Just d => pure (n, !(wasmDef globals n d))

getDef : Defs -> Name -> Core annot (CDef)
getDef defs n = case lookupGlobalExact n (gamma defs) of
    Nothing => throw (InternalError ("Compiling undefined name " ++ show n))
    Just d => case compexpr d of
        Nothing => throw (InternalError ("No compiled definition for " ++ show n))
        Just d => pure d

goExtract : CExp vars -> Core annot Name
goExtract (CLam _ body) = goExtract body
goExtract (CApp (CRef name) _) = pure name
goExtract e = throw (InternalError ("cannot extract export from internals: " ++ show e))

extractExport : CExp vars -> Core annot Name
extractExport exp = do
    CApp _ [_, l] <- pure exp
        | _ => throw (InternalError ("cannot extract export from: " ++ show exp))
    goExtract l

extractExportFromDef : CDef -> Core annot Name
extractExportFromDef (MkFun _ body) = extractExport body
extractExportFromDef d = throw (InternalError ("cannot extract export from: " ++ show d))

extractMain : CExp vars -> Core annot Name
extractMain (CApp _ [_, (CApp (CRef name) [])]) = pure name
extractMain e = throw (InternalError ("cannot extract main name from: " ++ show e))

findMain : (defs : List (Name, TSDef)) -> (main : Name) -> Core annot (Fin (length defs))
findMain [] main = throw (InternalError "export not defined")
findMain ((n, _) :: ns) main =
    if n == main then
        pure FZ
    else do
        idx <- findMain ns main
        pure (FS idx)

onlyDefs : List (Name, TSDef) -> List TSDef
onlyDefs [] = []
onlyDefs ((_, d) :: xs) = d :: onlyDefs xs

sameLength : (defs : List (Name, TSDef)) -> (length defs = length (onlyDefs defs))
sameLength [] = Refl
sameLength ((_, _) :: xs) = rewrite sameLength xs in Refl

mainToExport : Ref Ctxt Defs -> ClosedTerm -> Core annot Name
mainToExport c tm = do
    (ns, tags) <- findUsedNames tm
    defs <- get Ctxt
    main <- compileExp tags tm
    codeMainName <- extractMain main
    codeMainDef <- getDef defs codeMainName
    exportName <- extractExportFromDef codeMainDef
    pure exportName

||| Compile a Blodwen expression to wasm
compileToWasm : Ref Ctxt Defs -> ClosedTerm -> Core annot TSExp.Module
compileToWasm c tm = do
    exportName <- mainToExport c tm
    let fakeMain = the ClosedTerm (Ref Func exportName)
    (ns, tags) <- findUsedNames fakeMain
    defs <- get Ctxt
    compdefs <- traverse (getWasmDef ns defs) ns
    mainIdx <- findMain compdefs exportName
    let tsDefs = onlyDefs compdefs
    pure (MkModule tsDefs (rewrite sym (sameLength compdefs) in mainIdx))

||| Wasm implementation of the `compileExpr` interface.
compileExpr : Ref Ctxt Defs -> ClosedTerm -> (outfile : String) -> Core annot (Maybe String)
compileExpr c tm outfile = do
    let outn = outfile ++ ".wat"
    mod <- compileToWasm c tm
    Right wasm <- pure (translateToWasm mod)
        | Left err => throw (InternalError ("failed to compile to wasm: " ++ err))
    Right () <- coreLift $ writeFile outn wasm
        | Left err => throw (FileErr outn err)
    pure (Just outn)

||| TSExp implementation of the `compileExpr` interface.
compileExprTS : Ref Ctxt Defs -> ClosedTerm -> (outfile : String) -> Core annot (Maybe String)
compileExprTS c tm outfile = do
    let outn = outfile ++ ".ts"
    mod <- compileToWasm c tm
    Right wasm <- pure (the (Either String String) $ Right $ show mod)
        | Left err => throw (InternalError ("failed to compile to wasm: " ++ err))
    Right () <- coreLift $ writeFile outn wasm
        | Left err => throw (FileErr outn err)
    pure (Just outn)

||| Mir implementation of the `compileExpr` interface.
compileExprMir : Ref Ctxt Defs -> ClosedTerm -> (outfile : String) -> Core annot (Maybe String)
compileExprMir c tm outfile = do
    let outn = outfile ++ ".mir"
    mod <- compileToWasm c tm
    Right mir <- pure (Trans.run (TSExpToMir.translateModule mod) "")
        | Left err => throw (InternalError ("failed to compile to mir: " ++ err))
    let mirText = show mir
    Right () <- coreLift $ writeFile outn mirText
        | Left err => throw (FileErr outn err)
    pure (Just outn)

executeExpr : Ref Ctxt Defs -> ClosedTerm -> Core annot ()
executeExpr c tm = throw (InternalError "execute is not supported in wasm codegen")

||| Codegen wrapper for Wasm implementation.
export
codegenWasm : Codegen annot
codegenWasm = MkCG compileExpr executeExpr

||| Codegen wrapper for TSExp implementation.
export
codegenTS : Codegen annot
codegenTS = MkCG compileExprTS executeExpr

||| Codegen wrapper for Mir implementation.
export
codegenMir : Codegen annot
codegenMir = MkCG compileExprMir executeExpr
