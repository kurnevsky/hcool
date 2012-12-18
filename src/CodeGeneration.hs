module CodeGeneration where

import Semantics
import qualified Data.Map as Map
import Data.List
import Data.Maybe

data Command = Label Int                            |
               Add                                  |
               Sub                                  |
               Mul                                  |
               Div                                  |
               Ret                                  |
               Ldloc Int                            |
               Ldarg Int                            |
               Ldint Int                            |
               Ldstr String                         |
               Ldfld CType String String            |
               Stloc Int                            |
               Starg Int                            |
               Stfld CType String String            |
               Newobj String                        |
               Ceq                                  |
               Ldnull                               |
               Neg                                  |
               Clt                                  |
               Cgt                                  |
               Br Int                               |
               Brfalse Int                          |
               Brtrue Int                           |
               Callctor String                      |
               Pop                                  |
               Call CType String String [CType]     |
               Callvirt CType String String [CType] |
               Streq                                |
               Boxint                               |
               Boxbool                              |
               Isinst CType                         |
               Unboxint                             |
               Unboxbool                            |
               Throw String

data CVariableType = CVTField | CVTArgument | CVTLocal

type CGProgram = [CGClass]

--(Имя, Родитель, Поля, Конструктор, Методы)
type CGClass = (String, String, [(CType, String)], ([(CType, String)], [Command], Int), [CGMethod])

--(Имя, Тип результата, Аргументы, Локальные переменные, Команды, Размер стека)
type CGMethod = (String, CType, [(CType, String)], [(CType, String)], [Command], Int)

translateProgram :: Map.Map String String -> (String -> String -> Maybe (CFuncResult, [CType])) -> S2Program -> CGProgram
translateProgram parents classMappings program = map (translateClass parents classMappings) program

stackChange :: Command -> Int
stackChange (Label _) = 0
stackChange Add = -1
stackChange Sub = -1
stackChange Mul = -1
stackChange Div = -1
stackChange Ret = 0
stackChange (Ldloc _) = 1
stackChange (Ldarg _) = 1
stackChange (Ldint _) = 1
stackChange (Ldstr _) = 1
stackChange (Ldfld _ _ _) = 0
stackChange (Stloc _) = -1
stackChange (Starg _) = -1
stackChange (Stfld _ _ _) = -2
stackChange (Newobj _) = 1
stackChange Ceq = -1
stackChange Ldnull = 1
stackChange Neg = 0
stackChange Clt = -1
stackChange Cgt = -1
stackChange (Br _) = 0
stackChange (Brfalse _) = -1
stackChange (Brtrue _) = -1
stackChange (Callctor _) = -1
stackChange Pop = -1
stackChange (Call _ _ _ args) = -length args
stackChange (Callvirt _ _ _ args) = -length args
stackChange Streq = -1
stackChange Boxint = 0
stackChange Boxbool = 0
stackChange (Isinst _) = 0
stackChange Unboxint = 0
stackChange Unboxbool = 0
stackChange (Throw _) = 0

maxStackSize :: [Command] -> Int
maxStackSize cmds = maxStackSize' 0 0 cmds
        where maxStackSize' lastMax _ [] = lastMax
              maxStackSize' lastMax curSize (h:t) = let nextSize = curSize + stackChange h
                                                    in maxStackSize' (max lastMax nextSize) nextSize t

translateClass :: Map.Map String String -> (String -> String -> Maybe (CFuncResult, [CType])) -> S2Class -> CGClass
translateClass parents classMappings (selfName, parent, parentsFields, fields, methods) =
        let varMappings = Map.union (Map.fromList $ map (\(name, ctype, _) -> (name, (CVTField, ctype, 0))) fields) (Map.map (\ctype -> (CVTField, ctype, 0)) parentsFields)
            (ctorVars, ctorCmds) = translateFields [] [Callctor parent, Ldarg 0] parents classMappings selfName varMappings 0 fields
            ctorCmds' = reverse (Ret : ctorCmds)
            ctorVars' = reverse ctorVars
            translatedMethods = map (\(name, ctype, args, cexpr) -> translateMethod parents classMappings selfName varMappings name ctype args cexpr) methods
            createMethod = ("_create", CTObject, [], [], [Newobj selfName, Ret], 1)
        in (selfName,
            parent,
            map (\(name, ctype, _) -> (ctype, name)) fields,
            (ctorVars', ctorCmds', maxStackSize ctorCmds'),
            createMethod : translatedMethods)

translateMethod :: Map.Map String String -> (String -> String -> Maybe (CFuncResult, [CType])) -> String -> Map.Map String (CVariableType, CType, Int) -> String -> String -> [(String, String)] -> S2Expr -> CGMethod
translateMethod parents classMappings selfName varMappings name ctypeName args expr =
        let ctype = ctypeFromStringWithSelf selfName ctypeName
            args' = map (\(name', ctype') -> (ctypeFromStringWithSelf selfName ctype', name')) args
            varMappings' = Map.union (Map.fromList $ map (\(number, (ctype', name')) -> (name', (CVTArgument, ctype', number))) $ zip [1..] args') varMappings
            (vars, cmds, _) = translateExpr [] [] parents classMappings selfName varMappings' 0 expr
            cmds' = reverse (Ret : addBoxing ctype (getType expr) cmds)
            vars' = reverse vars
        in (name, ctype, args', vars', cmds', maxStackSize cmds')

translateFields :: [(CType, String)] -> [Command] -> Map.Map String String -> (String -> String -> Maybe (CFuncResult, [CType])) -> String -> Map.Map String (CVariableType, CType, Int) -> Int -> [S2Field] -> ([(CType, String)], [Command])
translateFields vars cmds _ _ _ _ _ [] =
        (vars, cmds)
translateFields vars cmds parents classMappings selfName varMappings nextLabel ((_, _, S2Void):t) =
        translateFields vars cmds parents classMappings selfName varMappings nextLabel t
translateFields vars cmds parents classMappings selfName varMappings nextLabel ((name, ctype, cexpr):t) =
        let (vars', cmds', nextLabel') = translateExpr vars (Ldarg 0 : cmds) parents classMappings selfName varMappings nextLabel cexpr
        in translateFields vars' (Stfld ctype selfName name : addBoxing ctype (getType cexpr) cmds') parents classMappings selfName varMappings nextLabel' t

addBoxing :: CType -> CType -> [Command] -> [Command]
addBoxing ctype1 ctype2 cmds = if ctype1 == CTObject
                               then if ctype2 == CTInt
                                    then Boxint : cmds
                                    else if ctype2 == CTBool
                                    then Boxbool : cmds
                                    else cmds
                               else cmds

addUnboxing :: CType -> [Command] -> [Command]
addUnboxing ctype cmds = if ctype == CTInt
                         then Unboxint : cmds
                         else if ctype == CTBool
                         then Unboxbool : cmds
                         else cmds

translateExpr :: [(CType, String)] -> [Command] -> Map.Map String String -> (String -> String -> Maybe (CFuncResult, [CType])) -> String -> Map.Map String (CVariableType, CType, Int) -> Int -> S2Expr -> ([(CType, String)], [Command], Int)
translateExpr _ _ _ _ _ _ _ S2Void =
        error "S2Void error."

translateExpr vars cmds _ _ _ _ nextLabel (S2Self _) =
        (vars, Ldarg 0 : cmds, nextLabel)

translateExpr vars cmds _ _ _ _ nextLabel S2True =
        (vars, Ldint 1 : cmds, nextLabel)

translateExpr vars cmds _ _ _ _ nextLabel S2False =
        (vars, Ldint 0 : cmds, nextLabel)

translateExpr vars cmds _ _ _ _ nextLabel (S2String str) =
        (vars, Ldstr str : cmds, nextLabel)

translateExpr vars cmds _ _ _ _ nextLabel (S2Integer val) =
        (vars, Ldint (fromIntegral val) : cmds, nextLabel)

translateExpr vars cmds _ _ selfName varMappings nextLabel (S2Variable _ name) =
        case varMappings Map.! name of
          (CVTField, ctype, _) -> (vars, Ldfld ctype selfName name : Ldarg 0 : cmds, nextLabel)
          (CVTArgument, _, number) -> (vars, Ldarg number : cmds, nextLabel)
          (CVTLocal, _, number) -> (vars, Ldloc number : cmds, nextLabel)

translateExpr vars cmds parents classMappings selfName varMappings nextLabel (S2Dot _ cexpr className methodName args) =
        let (vars', cmds', nextLabel') = translateExpr vars cmds parents classMappings selfName varMappings nextLabel cexpr
            (vars'', cmds'', nextLabel'') = translateArgs vars' (addBoxing (ctypeFromString classWithMethod) (getType cexpr) cmds') nextLabel' args
            translateArgs vars''' cmds''' nextLabel''' [] = (vars''', cmds''', nextLabel''')
            translateArgs vars''' cmds''' nextLabel''' (h:t) = let (vars'''', cmds'''', nextLabel'''') = translateExpr vars''' cmds''' parents classMappings selfName varMappings nextLabel''' h
                                                               in translateArgs vars'''' cmds'''' nextLabel'''' t
            allParents = case getType cexpr of
                           CTObject -> ["Object"]
                           CTInt -> ["Int", "Object"]
                           CTBool -> ["Bool", "Object"]
                           CTString -> ["String", "Object"]
                           CTClass name -> getAllParents parents name
            allMethods = map (\className' -> classMappings className' methodName) allParents
            classWithMethod = allParents !! (fromJust $ findIndex (/= Nothing) allMethods)
        in if className == ""
           then let (resultType, argsTypes) = head $ catMaybes allMethods
                in case resultType of
                     CRSelfType   -> (vars'', addUnboxing (getType cexpr) (Callvirt (ctypeFromString classWithMethod) classWithMethod methodName argsTypes : cmds''), nextLabel'')
                     CRType ctype -> (vars'', Callvirt ctype classWithMethod methodName argsTypes : cmds'', nextLabel'')
           else let Just (resultType, argsTypes) = classMappings className methodName
                in case resultType of
                     CRSelfType   -> (vars'', addUnboxing (getType cexpr) (Call (ctypeFromString className) className methodName argsTypes : cmds''), nextLabel'')
                     CRType ctype -> (vars'', Call ctype className methodName argsTypes : cmds'', nextLabel'')

translateExpr vars cmds _ _ selfName _ nextLabel (S2New _ "SELF_TYPE") =
        (vars, Callvirt CTObject selfName "_create" [] : Ldarg 0 : cmds, nextLabel)
translateExpr vars cmds _ _ _ _ nextLabel (S2New _ "Int") =
        (vars, Ldint 0 : cmds, nextLabel)
translateExpr vars cmds _ _ _ _ nextLabel (S2New _ "Bool") =
        (vars, Ldint 0 : cmds, nextLabel)
translateExpr vars cmds _ _ _ _ nextLabel (S2New _ "String") =
        (vars, Ldstr "" : cmds, nextLabel)
translateExpr vars cmds _ _ _ _ nextLabel (S2New _ ctype) =
        (vars, Newobj ctype : cmds, nextLabel)

translateExpr vars cmds parents classMappings selfName varMappings nextLabel (S2UnaryOp _ "not" expr) =
        let (vars', cmds', nextLabel') = translateExpr vars cmds parents classMappings selfName varMappings nextLabel expr
        in (vars', Ceq : Ldint 0 : cmds', nextLabel')
translateExpr vars cmds parents classMappings selfName varMappings nextLabel (S2UnaryOp _ "isvoid" expr) =
        let (vars', cmds', nextLabel') = translateExpr vars cmds parents classMappings selfName varMappings nextLabel expr
        in (vars', Ceq : Ldnull : cmds', nextLabel')
translateExpr vars cmds parents classMappings selfName varMappings nextLabel (S2UnaryOp _ "~" expr) =
        let (vars', cmds', nextLabel') = translateExpr vars cmds parents classMappings selfName varMappings nextLabel expr
        in (vars', Neg : cmds', nextLabel')

translateExpr vars cmds parents classMappings selfName varMappings nextLabel (S2BinaryOp _ "=" expr1 expr2) =
        let (vars', cmds', nextLabel') = translateExpr vars cmds parents classMappings selfName varMappings nextLabel expr1
            (vars'', cmds'', nextLabel'') = translateExpr vars' cmds' parents classMappings selfName varMappings nextLabel' expr2
        in case getType expr1 of
             CTString -> (vars'', Streq : cmds'', nextLabel'')
             _        -> (vars'', Ceq : cmds'', nextLabel'')
translateExpr vars cmds parents classMappings selfName varMappings nextLabel (S2BinaryOp _ "<=" expr1 expr2) =
        let (vars', cmds', nextLabel') = translateExpr vars cmds parents classMappings selfName varMappings nextLabel expr1
            (vars'', cmds'', nextLabel'') = translateExpr vars' cmds' parents classMappings selfName varMappings nextLabel' expr2
        in (vars'', Ceq : Ldint 0 : Cgt : cmds'', nextLabel'')
translateExpr vars cmds parents classMappings selfName varMappings nextLabel (S2BinaryOp _ "<" expr1 expr2) =
        let (vars', cmds', nextLabel') = translateExpr vars cmds parents classMappings selfName varMappings nextLabel expr1
            (vars'', cmds'', nextLabel'') = translateExpr vars' cmds' parents classMappings selfName varMappings nextLabel' expr2
        in (vars'', Clt : cmds'', nextLabel'')
translateExpr vars cmds parents classMappings selfName varMappings nextLabel (S2BinaryOp _ "+" expr1 expr2) =
        let (vars', cmds', nextLabel') = translateExpr vars cmds parents classMappings selfName varMappings nextLabel expr1
            (vars'', cmds'', nextLabel'') = translateExpr vars' cmds' parents classMappings selfName varMappings nextLabel' expr2
        in (vars'', Add : cmds'', nextLabel'')
translateExpr vars cmds parents classMappings selfName varMappings nextLabel (S2BinaryOp _ "-" expr1 expr2) =
        let (vars', cmds', nextLabel') = translateExpr vars cmds parents classMappings selfName varMappings nextLabel expr1
            (vars'', cmds'', nextLabel'') = translateExpr vars' cmds' parents classMappings selfName varMappings nextLabel' expr2
        in (vars'', Sub : cmds'', nextLabel'')
translateExpr vars cmds parents classMappings selfName varMappings nextLabel (S2BinaryOp _ "*" expr1 expr2) =
        let (vars', cmds', nextLabel') = translateExpr vars cmds parents classMappings selfName varMappings nextLabel expr1
            (vars'', cmds'', nextLabel'') = translateExpr vars' cmds' parents classMappings selfName varMappings nextLabel' expr2
        in (vars'', Mul : cmds'', nextLabel'')
translateExpr vars cmds parents classMappings selfName varMappings nextLabel (S2BinaryOp _ "/" expr1 expr2) =
        let (vars', cmds', nextLabel') = translateExpr vars cmds parents classMappings selfName varMappings nextLabel expr1
            (vars'', cmds'', nextLabel'') = translateExpr vars' cmds' parents classMappings selfName varMappings nextLabel' expr2
        in (vars'', Div : cmds'', nextLabel'')

translateExpr vars cmds parents classMappings selfName varMappings nextLabel (S2Block _ exprs) =
        translateExprs vars cmds nextLabel exprs
        where translateExprs vars' cmds' nextLabel' [expr] = let (vars'', cmds'', nextLabel'') = translateExpr vars' cmds' parents classMappings selfName varMappings nextLabel' expr
                                                             in (vars'', cmds'', nextLabel'')
              translateExprs vars' cmds' nextLabel' (h:t) = let (vars'', cmds'', nextLabel'') = translateExpr' vars' cmds' parents classMappings selfName varMappings nextLabel' h
                                                            in translateExprs vars'' cmds'' nextLabel'' t
              translateExprs _ _ _ [] = error "Empty block in translation."

translateExpr vars cmds parents classMappings selfName varMappings nextLabel (S2If ctype cond expr1 expr2) =
        let (vars', cmds', nextLabel') = translateExpr vars cmds parents classMappings selfName varMappings (nextLabel + 2) cond
            (vars'', cmds'', nextLabel'') = translateExpr vars' (Brfalse nextLabel : cmds') parents classMappings selfName varMappings nextLabel' expr1
            (vars''', cmds''', nextLabel''') = translateExpr vars'' (Label nextLabel : Br (nextLabel + 1) : addBoxing ctype (getType expr1) cmds'') parents classMappings selfName varMappings nextLabel'' expr2
        in (vars''', Label (nextLabel + 1) : addBoxing ctype (getType expr2) cmds''', nextLabel''')

translateExpr vars cmds parents classMappings selfName varMappings nextLabel (S2While _ cond expr) =
        let (vars', cmds', nextLabel') = translateExpr vars (Label nextLabel : cmds) parents classMappings selfName varMappings (nextLabel + 2) cond
            (vars'', cmds'', nextLabel'') = translateExpr' vars' (Brfalse (nextLabel + 1) : cmds') parents classMappings selfName varMappings nextLabel' expr
        in (vars'', Ldnull : Label (nextLabel + 1) : Br nextLabel : cmds'', nextLabel'')

translateExpr vars cmds parents classMappings selfName varMappings nextLabel (S2Let _ lets expr) =
        translateLet vars cmds varMappings nextLabel lets
        where translateLet vars' cmds' varMappings' nextLabel' [] =
                        translateExpr vars' cmds' parents classMappings selfName varMappings' nextLabel' expr
              translateLet vars' cmds' varMappings' nextLabel' ((name, ctypeName, S2Void):t) =
                        let ctype = ctypeFromStringWithSelf selfName ctypeName
                        in translateLet ((ctype, name) : vars') cmds' (Map.insert name (CVTLocal, ctype, length vars') varMappings') nextLabel' t
              translateLet vars' cmds' varMappings' nextLabel' ((name, ctypeName, expr'):t) =
                        let ctype = ctypeFromStringWithSelf selfName ctypeName
                            (vars'', cmds'', nextLabel'') = translateExpr vars' cmds' parents classMappings selfName varMappings' nextLabel' expr'
                        in translateLet ((ctype, name) : vars'') (Stloc (length vars'') : cmds'') (Map.insert name (CVTLocal, ctype, length vars') varMappings') nextLabel'' t

translateExpr vars cmds parents classMappings selfName varMappings nextLabel (S2Case ctype expr cases) =
        translateCase ((CTObject, "caseobj") : vars') (Stloc (length vars) : addBoxing CTObject (getType expr) cmds') (nextLabel' + 1) cases
        where (vars', cmds', nextLabel') = translateExpr vars cmds parents classMappings selfName varMappings nextLabel expr
              translateCase vars'' cmds'' nextLabel'' [] = (vars'', Label nextLabel : Throw "Case error." : cmds'', nextLabel'')
              translateCase vars'' cmds'' nextLabel'' ((name, ctype', expr'):t) =
                        let (vars''', cmds''', nextLabel''') = translateExpr ((ctype', name) : vars'') (Stloc (length vars'') : addUnboxing ctype' (Ldloc (length vars') : Brfalse nextLabel'' : Isinst ctype' : Ldloc (length vars') : cmds'')) parents classMappings selfName (Map.insert name (CVTLocal, ctype', length vars'') varMappings) (nextLabel'' + 1) expr'
                        in translateCase vars''' (Label nextLabel'' : Br nextLabel' : addBoxing ctype (getType expr') cmds''') nextLabel''' t

translateExpr vars cmds parents classMappings selfName varMappings nextLabel (S2Assign _ name expr) =
        let (vars', cmds', nextLabel') = translateExpr vars cmds parents classMappings selfName varMappings nextLabel expr
            (vars'', cmds'', nextLabel'') = translateExpr vars (Ldarg 0 : cmds) parents classMappings selfName varMappings nextLabel expr
        in case varMappings Map.! name of
             (CVTField, ctype, _) -> (vars'', Ldfld ctype selfName name : Ldarg 0 : Stfld ctype selfName name : cmds'', nextLabel'')
             (CVTArgument, _, number) -> (vars', Ldarg number : Starg number : cmds', nextLabel')
             (CVTLocal, _, number) -> (vars', Ldloc number : Stloc number : cmds', nextLabel')

translateExpr _ _ _ _ _ _ _ _ = error "Error in translateExpr."

translateExpr' :: [(CType, String)] -> [Command] -> Map.Map String String -> (String -> String -> Maybe (CFuncResult, [CType])) -> String -> Map.Map String (CVariableType, CType, Int) -> Int -> S2Expr -> ([(CType, String)], [Command], Int)
translateExpr' _ _ _ _ _ _ _ S2Void =
        error "CVoid error."

translateExpr' vars cmds _ _ _ _ nextLabel (S2Self _) =
        (vars, cmds, nextLabel)

translateExpr' vars cmds _ _ _ _ nextLabel S2True =
        (vars, cmds, nextLabel)

translateExpr' vars cmds _ _ _ _ nextLabel S2False =
        (vars, cmds, nextLabel)

translateExpr' vars cmds _ _ _ _ nextLabel (S2String _) =
        (vars, cmds, nextLabel)

translateExpr' vars cmds _ _ _ _ nextLabel (S2Integer _) =
        (vars, cmds, nextLabel)

translateExpr' vars cmds _ _ _ _ nextLabel (S2Variable _ _) =
        (vars, cmds, nextLabel)

translateExpr' vars cmds parents classMappings selfName varMappings nextLabel (S2Dot pos cexpr className methodName args) =
        let (vars', cmds', nextLabel') = translateExpr vars cmds parents classMappings selfName varMappings nextLabel (S2Dot pos cexpr className methodName args)
        in (vars', Pop : cmds', nextLabel')

translateExpr' vars cmds parents classMappings selfName varMappings nextLabel (S2New pos ctype) =
        let (vars', cmds', nextLabel') = translateExpr vars cmds parents classMappings selfName varMappings nextLabel (S2New pos ctype)
        in (vars', Pop : cmds', nextLabel')

translateExpr' vars cmds parents classMappings selfName varMappings nextLabel (S2UnaryOp _ _ expr) =
        translateExpr' vars cmds parents classMappings selfName varMappings nextLabel expr

translateExpr' vars cmds parents classMappings selfName varMappings nextLabel (S2BinaryOp _ _ expr1 expr2) =
        let (vars', cmds', nextLabel') = translateExpr' vars cmds parents classMappings selfName varMappings nextLabel expr1
        in translateExpr' vars' cmds' parents classMappings selfName varMappings nextLabel' expr2

translateExpr' vars cmds parents classMappings selfName varMappings nextLabel (S2Block _ exprs) =
        translateExprs vars cmds nextLabel exprs
        where translateExprs vars' cmds' nextLabel' [] = (vars', cmds', nextLabel')
              translateExprs vars' cmds' nextLabel' (h:t) = let (vars'', cmds'', nextLabel'') = translateExpr' vars' cmds' parents classMappings selfName varMappings nextLabel' h
                                                            in translateExprs vars'' cmds'' nextLabel'' t

translateExpr' vars cmds parents classMappings selfName varMappings nextLabel (S2If _ cond expr1 expr2) =
        let (vars', cmds', nextLabel') = translateExpr vars cmds parents classMappings selfName varMappings (nextLabel + 2) cond
            (vars'', cmds'', nextLabel'') = translateExpr' vars' (Brfalse nextLabel : cmds') parents classMappings selfName varMappings nextLabel' expr1
            (vars''', cmds''', nextLabel''') = translateExpr' vars'' (Label nextLabel : Br (nextLabel + 1) : cmds'') parents classMappings selfName varMappings nextLabel'' expr2
        in (vars''', Label (nextLabel + 1) : cmds''', nextLabel''')

translateExpr' vars cmds parents classMappings selfName varMappings nextLabel (S2While _ cond expr) =
        let (vars', cmds', nextLabel') = translateExpr vars (Label nextLabel : cmds) parents classMappings selfName varMappings (nextLabel + 2) cond
            (vars'', cmds'', nextLabel'') = translateExpr' vars' (Brfalse (nextLabel + 1) : cmds') parents classMappings selfName varMappings nextLabel' expr
        in (vars'', Label (nextLabel + 1) : Br nextLabel : cmds'', nextLabel'')

translateExpr' vars cmds parents classMappings selfName varMappings nextLabel (S2Let _ lets expr) =
        translateLet vars cmds varMappings nextLabel lets
        where translateLet vars' cmds' varMappings' nextLabel' [] =
                        translateExpr' vars' cmds' parents classMappings selfName varMappings' nextLabel' expr
              translateLet vars' cmds' varMappings' nextLabel' ((name, ctypeName, S2Void):t) =
                        let ctype = ctypeFromStringWithSelf selfName ctypeName
                        in translateLet ((ctype, name) : vars') cmds' (Map.insert name (CVTLocal, ctype, length vars') varMappings') nextLabel' t
              translateLet vars' cmds' varMappings' nextLabel' ((name, ctypeName, expr'):t) =
                        let ctype = ctypeFromStringWithSelf selfName ctypeName
                            (vars'', cmds'', nextLabel'') = translateExpr vars' cmds' parents classMappings selfName varMappings' nextLabel' expr'
                        in translateLet ((ctype, name) : vars'') (Stloc (length vars'') : cmds'') (Map.insert name (CVTLocal, ctype, length vars') varMappings') nextLabel'' t

translateExpr' vars cmds parents classMappings selfName varMappings nextLabel (S2Case _ expr cases) =
        translateCase ((CTObject, "caseobj") : vars') (Stloc (length vars) : addBoxing CTObject (getType expr) cmds') (nextLabel' + 1) cases
        where (vars', cmds', nextLabel') = translateExpr vars cmds parents classMappings selfName varMappings nextLabel expr
              translateCase vars'' cmds'' nextLabel'' [] = (vars'', Label nextLabel : Throw "Case error." : cmds'', nextLabel'')
              translateCase vars'' cmds'' nextLabel'' ((name, ctype', expr'):t) =
                        let (vars''', cmds''', nextLabel''') = translateExpr' ((ctype', name) : vars'') (Stloc (length vars'') : addUnboxing ctype' (Ldloc (length vars') : Brfalse nextLabel'' : Isinst ctype' : Ldloc (length vars') : cmds'')) parents classMappings selfName (Map.insert name (CVTLocal, ctype', length vars'') varMappings) (nextLabel'' + 1) expr'
                        in translateCase vars''' (Label nextLabel'' : Br nextLabel' : cmds''') nextLabel''' t

translateExpr' vars cmds parents classMappings selfName varMappings nextLabel (S2Assign _ name expr) =
        let (vars', cmds', nextLabel') = translateExpr vars cmds parents classMappings selfName varMappings nextLabel expr
            (vars'', cmds'', nextLabel'') = translateExpr vars (Ldarg 0 : cmds) parents classMappings selfName varMappings nextLabel expr
        in case varMappings Map.! name of
             (CVTField, ctype, _) -> (vars'', Stfld ctype selfName name : cmds'', nextLabel'')
             (CVTArgument, _, number) -> (vars', Starg number : cmds', nextLabel')
             (CVTLocal, _, number) -> (vars', Stloc number : cmds', nextLabel')