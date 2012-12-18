module Semantics where

import qualified Data.Map as Map
import Data.Maybe
import Data.List
import Data.Either
import Syntax

data CType = CTObject | CTInt | CTBool | CTString | CTClass String

type S2Program = [S2Class]

type S2Class = (String, String, Map.Map String CType, [S2Field], [S2Method])

type S2Method = (String, String, [(String, String)], S2Expr)

type S2Field = (String, CType, S2Expr)

data S2Expr = S2Void                                         |
              S2Self CType                                   |
              S2True                                         |
              S2False                                        |
              S2String String                                |
              S2Integer Integer                              |
              S2Variable CType String                        |
              S2Dot CType S2Expr String String [S2Expr]      |
              S2New CType String                             |
              S2UnaryOp CType String S2Expr                  |
              S2BinaryOp CType String S2Expr S2Expr          |
              S2Block CType [S2Expr]                         |
              S2If CType S2Expr S2Expr S2Expr                |
              S2While CType S2Expr S2Expr                    |
              S2Let CType [(String, String, S2Expr)] S2Expr  |
              S2Case CType S2Expr [(String, CType, S2Expr)] |
              S2Assign CType String S2Expr

getType :: S2Expr -> CType
getType S2Void = CTObject
getType (S2Self ctype) = ctype
getType S2True = CTBool
getType S2False = CTBool
getType (S2String _) = CTString
getType (S2Integer _) = CTInt
getType (S2Variable ctype _) = ctype
getType (S2Dot ctype _ _ _ _) = ctype
getType (S2New ctype _) = ctype
getType (S2UnaryOp ctype _ _) = ctype
getType (S2BinaryOp ctype _ _ _) = ctype
getType (S2Block ctype _) = ctype
getType (S2If ctype _ _ _) = ctype
getType (S2While ctype _ _) = ctype
getType (S2Let ctype _ _) = ctype
getType (S2Case ctype _ _) = ctype
getType (S2Assign ctype _ _) = ctype

instance Eq CType where
        CTObject == CTObject = True
        CTInt == CTInt = True
        CTBool == CTBool = True
        CTString == CTString = True
        CTClass name1 == CTClass name2 = name1 == name2
        _ == _ = False

instance Show CType where
        showsPrec _ CTObject = showString "Object"
        showsPrec _ CTInt = showString "Int"
        showsPrec _ CTBool = showString "Bool"
        showsPrec _ CTString = showString "String"
        showsPrec _ (CTClass name) = showString name

type CMappings = (Map.Map String CType, Map.Map (String, String) (CType, [CType]), String)

findDuplicate :: Eq a => [a] -> Maybe a
findDuplicate [] = Nothing
findDuplicate (h:t) = if elem h t then Just h else findDuplicate t

isConforms :: Map.Map String String -> CType -> CType -> Bool
isConforms parents a b = getCommonAncestor parents [a, b] == b

foldResult :: [Either [String] ()] -> Either [String] ()
foldResult result = if not $ null $ lefts result
                    then Left (concat $ lefts result)
                    else Right ()

semanticsCheck :: S1Program -> Either [String] (S2Program, Map.Map String String, String -> String -> Maybe (CFuncResult, [CType]))
semanticsCheck cprogram = let classesFields = Map.fromList $ ("Object", Map.empty) : ("IO", Map.empty) : map (\(_, name, _, fields, _) -> (name, Map.fromList $ map (\(_, name', ctype, _) -> (name', ctypeFromString ctype)) fields)) cprogram
                              parentsFields name = foldl1 Map.union $ map (classesFields Map.!) $ tail $ getAllParents parents name
                              classesMethods = Map.fromList $ map (\cclass@(_, name, _, _, _) -> (name, getClassMethods cclass)) cprogram
                              parents = Map.fromList $ ("IO", "Object") : (map (\(_, name, parent, _, _) -> (name, parent)) cprogram)
                              classMappings "Object" "abort" = Just (CRType CTObject, [])
                              classMappings "Object" "type_name" = Just (CRType CTString, [])
                              classMappings "Object" "copy" = Just (CRSelfType, [])
                              classMappings "String" "length" = Just (CRType CTInt, [])
                              classMappings "String" "concat" = Just (CRType CTString, [CTString])
                              classMappings "String" "substr" = Just (CRType CTString, [CTInt, CTInt])
                              classMappings "IO" "out_string" = Just (CRSelfType, [CTString])
                              classMappings "IO" "out_int" = Just (CRSelfType, [CTInt])
                              classMappings "IO" "in_string" = Just (CRType CTString, [])
                              classMappings "IO" "in_int" = Just (CRType CTInt, [])
                              classMappings className methodName = Map.lookup className classesMethods >>= Map.lookup methodName
                          in do checkClassesParent parents cprogram
                                checkDuplicates cprogram
                                checkClassesSignatures parents cprogram
                                checkMain classMappings
                                newProgram <- checkClassesExprs parents parentsFields classMappings cprogram
                                Right (newProgram, parents, classMappings)

checkMain :: (String -> String -> Maybe (CFuncResult, [CType])) -> Either [String] ()
checkMain classMappings = case classMappings "Main" "main" of
                            Nothing      -> Left ["Main class or method doesn't exists."]
                            Just (_, []) -> Right ()
                            _            -> Left ["Main method shouldn't contain arguments."]

checkClassFields :: Map.Map String String -> Map.Map String CType -> (String -> String -> Maybe (CFuncResult, [CType])) -> S1Class -> Either [String] ([S2Field], Map.Map String CType)
checkClassFields parents parentsFields classMappings (_, className, _, fields, _) =
        checkClassFields' parentsFields [] (map (\(pos, name, ctype, cexpr) -> (pos, name, ctypeFromStringWithSelf className ctype, cexpr)) fields)
        where checkClassFields' varMappings newFields [] = Right (reverse newFields, varMappings)
              checkClassFields' varMappings newFields ((pos, name, ctype, cexpr):t) = if case ctype of CTClass name' -> Map.notMember name' parents; _ -> False
                                                                                      then Left ["Unknown type: " ++ show ctype ++ " at " ++ show pos]
                                                                                      else do s2expr <- getExprType parents varMappings classMappings className cexpr
                                                                                              let exprType = getType s2expr
                                                                                              if cexpr /= S1Void && not (isConforms parents exprType ctype)
                                                                                                then Left ["Unconforms types: " ++ show exprType ++ " and " ++ show ctype ++ " at " ++ show pos]
                                                                                                else checkClassFields' (Map.insert name ctype varMappings) ((name, ctype, s2expr) : newFields) t

checkClassMethods :: Map.Map String String -> Map.Map String CType -> (String -> String -> Maybe (CFuncResult, [CType])) -> S1Class -> Either [String] [S2Method]
checkClassMethods parents varMappings classMappings (_, selfName, _, _, methods) =
        let newMethods = map (\(pos, name, ctype, args, expr) -> checkMethod pos name ctype args expr) methods
            methodErrors = concat $ lefts newMethods
        in if not $ null methodErrors
           then Left methodErrors
           else Right (rights newMethods)
        where checkMethod pos name resultTypeName args expr = do let argsMappings = Map.fromList $ map (\(name', ctype) -> (name', ctypeFromString ctype)) args
                                                                     resultType = ctypeFromStringWithSelf selfName resultTypeName
                                                                 s2expr <- getExprType parents (Map.union argsMappings varMappings) classMappings selfName expr
                                                                 let exprType = getType s2expr
                                                                 if not $ isConforms parents exprType resultType
                                                                   then Left ["Unconforms types: " ++ show resultTypeName ++ " and " ++ show exprType ++ " at " ++ show pos]
                                                                   else Right (name, resultTypeName, args, s2expr)

checkClassExprs :: Map.Map String String -> Map.Map String CType -> (String -> String -> Maybe (CFuncResult, [CType])) -> S1Class -> Either [String] ([S2Field], [S2Method])
checkClassExprs parents parentsFields classMappings cclass =
        do (classFields, varMappings) <- checkClassFields parents parentsFields classMappings cclass
           classMethods <- checkClassMethods parents varMappings classMappings cclass
           Right (classFields, classMethods)

checkClassesExprs :: Map.Map String String -> (String -> Map.Map String CType) -> (String -> String -> Maybe (CFuncResult, [CType])) -> S1Program -> Either [String] S2Program
checkClassesExprs parents parentsFields classMappings program =
        let result = map (\cclass@(_, name, _, _, _) -> checkClassExprs parents (parentsFields name) classMappings cclass) program
        in if not $ null $ lefts result
           then Left (concat $ lefts result)
           else Right (map (\((_, name, parent, _, _), (fields, methods)) -> (name, parent, parentsFields name, fields, methods)) $ zip program $ rights result)

checkClassSignatures :: Map.Map String String -> S1Class -> Either [String] ()
checkClassSignatures parents (_, _, _, _, methods) = let signatureErrors = concat $ lefts $ map (\(pos, _, ctype, args, _) -> checkSignature pos ctype args) methods
                                                     in if not $ null signatureErrors
                                                        then Left signatureErrors
                                                        else Right ()
        where checkSignature pos resultType args = let argsErrors = lefts $ map (\(_, ctype) -> if isTypeValid ctype then Right () else Left ("Unknown type: " ++ show ctype ++ " at " ++ show pos)) args
                                                       duplicate = findDuplicate $ map fst args
                                                   in if not $ resultType == "SELF_TYPE" || isTypeValid resultType
                                                      then Left ["Unknown result type: " ++ resultType ++ " at " ++ show pos]
                                                      else if not $ null argsErrors
                                                      then Left argsErrors
                                                      else if duplicate /= Nothing
                                                      then Left ["Duplicate argument name: " ++ fromJust duplicate ++ " at " ++ show pos]
                                                      else Right ()
              isTypeValid str = case ctypeFromString str of
                                  CTClass "Object" -> True
                                  CTClass _ -> Map.member str parents
                                  _ -> True

checkClassesSignatures :: Map.Map String String -> S1Program -> Either [String] ()
checkClassesSignatures parents program = foldResult $ map (checkClassSignatures parents) program

checkClassesParent :: Map.Map String String -> S1Program -> Either [String] ()
checkClassesParent parents program =
        let unknownParents = filter (\(_, name) -> name /= "Object" && Map.notMember name parents) $ map (\(pos, _, parent, _, _) -> (pos, parent)) program
        in if not $ null unknownParents
           then Left (map (\(pos, name) -> "Unknown class name: " ++ name ++ " at " ++ (show pos)) unknownParents)
           else Right ()

checkDuplicates :: S1Program -> Either [String] ()
checkDuplicates program =
        let duplicate = findDuplicate (map (\(_, name, _, _, _) -> name) program)
        in if duplicate /= Nothing
           then Left ["Duplicate class name: " ++ fromJust duplicate]
           else Right ()

getAllParents :: Map.Map String String -> String -> [String]
getAllParents _ "Object" = ["Object"]
getAllParents parents name = name : (getAllParents parents $ parents Map.! name)

data CFuncResult = CRSelfType | CRType CType

instance Eq CFuncResult where
        CRSelfType == CRSelfType = True
        CRType ctype1 == CRType ctype2 = ctype1 == ctype2
        _ == _ = False

getClassMethods :: S1Class -> Map.Map String (CFuncResult, [CType])
getClassMethods (_, className, _, _, methods) =
        Map.fromList $
        map (\(_, name, ctype, args, _) -> (name, (if ctype == "SELF_TYPE"
                                                   then CRSelfType else
                                                   CRType (ctypeFromString ctype), map (ctypeFromStringWithSelf className . snd) args))) $
        methods

getCommonAncestor :: Map.Map String String -> [CType] -> CType
getCommonAncestor parents ctypes = if length ctypes == 1
                                   then head ctypes
                                   else if elem CTObject ctypes
                                   then CTObject
                                   else if elem CTInt ctypes
                                   then if find (/= CTInt) ctypes /= Nothing then CTObject else CTInt
                                   else if elem CTBool ctypes
                                   then if find (/= CTBool) ctypes /= Nothing then CTObject else CTBool
                                   else if elem CTString ctypes
                                   then if find (/= CTString) ctypes /= Nothing then CTObject else CTString
                                   else let commonAncestor = getCommonAncestor' parents (map (\(CTClass name) -> name) ctypes)
                                        in if commonAncestor == "Object" then CTObject else CTClass commonAncestor

getCommonAncestor' :: Map.Map String String -> [String] -> String
getCommonAncestor' parents names = if elem "Object" names
                                   then "Object"
                                   else getCommonAncestor'' "Object" $ map (\name -> tail $ reverse $ getAllParents parents name) names

getCommonAncestor'' :: String -> [[String]] -> String
getCommonAncestor'' commonAncestor parents = let heads = map head parents
                                                 tails' = map tail parents
                                             in if not (elem [] parents) && all (== head heads) (tail heads)
                                                then getCommonAncestor'' (head heads) tails'
                                                else commonAncestor

ctypeFromString :: String -> CType
ctypeFromString "Object" = CTObject
ctypeFromString "Int" = CTInt
ctypeFromString "Bool" = CTBool
ctypeFromString "String" = CTString
ctypeFromString str = CTClass str

ctypeFromStringWithSelf :: String -> String -> CType
ctypeFromStringWithSelf selfName "SELF_TYPE" = CTClass selfName
ctypeFromStringWithSelf _ str = ctypeFromString str

isClass :: CType -> Bool
isClass (CTClass _) = True
isClass _ = False

getExprType :: Map.Map String String -> Map.Map String CType -> (String -> String -> Maybe (CFuncResult, [CType])) -> String -> S1Expr -> Either [String] S2Expr
getExprType _ _ _ _ S1Void = Right S2Void
getExprType _ _ _ selfName (S1Self _) = Right (S2Self (CTClass selfName))
getExprType _ _ _ _ (S1True _) = Right S2True
getExprType _ _ _ _ (S1False _) = Right S2False
getExprType _ _ _ _ (S1String _ str) = Right (S2String str)
getExprType _ _ _ _ (S1Integer pos val) = if val < -2147483648 || val > 2147483647
                                          then Left ["Too big integer at " ++ show pos]
                                          else Right (S2Integer val)
getExprType _ varMappings _ _ (S1Variable pos name) = if Map.notMember name varMappings
                                                      then Left ["Unknown variable name: " ++ name ++ " at " ++ show pos]
                                                      else Right (S2Variable (varMappings Map.! name) name)
getExprType parents varMappings classMappings selfName (S1Dot pos cexpr className methodName args) =
        do s2expr <- getExprType parents varMappings classMappings selfName cexpr
           let cexprType = getType s2expr
               allParents = case cexprType of
                              CTObject -> ["Object"]
                              CTInt -> ["Int", "Object"]
                              CTBool -> ["Bool", "Object"]
                              CTString -> ["String", "Object"]
                              CTClass name -> getAllParents parents name
               ctype = ctypeFromString className
               argsS2exprs = rights $ map (getExprType parents varMappings classMappings selfName) args
               argsTypes = map getType argsS2exprs
               argsErrors = lefts $ map (getExprType parents varMappings classMappings selfName) args
               checkSignature Nothing = Left ["Method doesn'n exists: " ++ methodName ++ " at " ++ show pos]
               checkSignature (Just (resultType, signatureArgs)) = if any (\(signatureArg, arg) -> not $ isConforms parents arg signatureArg) $ zip signatureArgs argsTypes
                                                                   then Left ["Signature mismatch: " ++ methodName ++ " at " ++ show pos]
                                                                   else case resultType of
                                                                          CRSelfType -> Right (S2Dot cexprType s2expr className methodName argsS2exprs)
                                                                          CRType ctype' -> Right (S2Dot ctype' s2expr className methodName argsS2exprs)
           if not $ null argsErrors
             then Left (concat argsErrors)
             else if className /= ""
                  then if isClass ctype && Map.notMember className parents
                       then Left ["Unknown type: " ++ className ++ " at " ++ show pos]
                       else if not $ elem className allParents
                       then Left ["Unconforms types: " ++ show className ++ " and " ++ show cexprType ++ " at " ++ show pos]
                       else checkSignature (classMappings className methodName)
                  else checkSignature $ (\methods -> if null methods then Nothing else Just (head methods)) $ catMaybes $ map (\parent -> classMappings parent methodName) allParents
getExprType parents _ _ selfName (S1New pos typeName) =
        let ctype = ctypeFromStringWithSelf selfName typeName
        in if isClass ctype && typeName /= "SELF_TYPE" && Map.notMember typeName parents
           then Left ["Unknown type: " ++ typeName ++ " at " ++ show pos]
           else Right (S2New ctype typeName)
getExprType parents varMappings classMappings selfName (S1UnaryOp pos "not" cexpr) =
        do s2expr <- getExprType parents varMappings classMappings selfName cexpr
           let ctype = getType s2expr
           if ctype == CTBool
             then Right (S2UnaryOp CTBool "not" s2expr)
             else Left ["Expected type Bool, but got " ++ show ctype ++ " at " ++ show pos]
getExprType parents varMappings classMappings selfName (S1UnaryOp _ "isvoid" cexpr) =
        do s2expr <- getExprType parents varMappings classMappings selfName cexpr
           Right (S2UnaryOp CTBool "isvoid" s2expr)
getExprType parents varMappings classMappings selfName (S1UnaryOp pos "~" cexpr) =
        do s2expr <- getExprType parents varMappings classMappings selfName cexpr
           let ctype = getType s2expr
           if ctype == CTInt
             then Right (S2UnaryOp CTInt "~" s2expr)
             else Left ["Expected type Int, but got " ++ show ctype ++ " at " ++ show pos]
getExprType parents varMappings classMappings selfName (S1BinaryOp pos op cexpr1 cexpr2) | op == "<=" || op == "<" || op == "+" || op == "-" || op == "*" || op == "/" =
        do s2expr1 <- getExprType parents varMappings classMappings selfName cexpr1
           s2expr2 <- getExprType parents varMappings classMappings selfName cexpr2
           let ctype1 = getType s2expr1
               ctype2 = getType s2expr2
           if ctype1 == CTInt && ctype2 == CTInt
             then if op == "<=" || op == "<"
                  then Right (S2BinaryOp CTBool op s2expr1 s2expr2)
                  else Right (S2BinaryOp CTInt op s2expr1 s2expr2)
             else if ctype1 /= CTInt
             then Left ["Expected type Int, but got " ++ show ctype1 ++ " at " ++ show pos]
             else Left ["Expected type Int, but got " ++ show ctype2 ++ " at " ++ show pos]
getExprType parents varMappings classMappings selfName (S1BinaryOp pos "=" cexpr1 cexpr2) =
        do s2expr1 <- getExprType parents varMappings classMappings selfName cexpr1
           s2expr2 <- getExprType parents varMappings classMappings selfName cexpr2
           let ctype1 = getType s2expr1
               ctype2 = getType s2expr2
           case (ctype1, ctype2) of
             (CTInt, CTInt) -> Right (S2BinaryOp CTBool "=" s2expr1 s2expr2)
             (CTBool, CTBool) -> Right (S2BinaryOp CTBool "=" s2expr1 s2expr2)
             (CTString, CTString) -> Right (S2BinaryOp CTBool "=" s2expr1 s2expr2)
             (CTInt, _) -> Left ["Expected type Int, but got " ++ show ctype2 ++ " at " ++ show pos]
             (CTBool, _) -> Left ["Expected type Bool, but got " ++ show ctype2 ++ " at " ++ show pos]
             (CTString, _) -> Left ["Expected type String, but got " ++ show ctype2 ++ " at " ++ show pos]
             (_, CTInt) -> Left ["Expected type Int, but got " ++ show ctype1 ++ " at " ++ show pos]
             (_, CTBool) -> Left ["Expected type Bool, but got " ++ show ctype1 ++ " at " ++ show pos]
             (_, CTString) -> Left ["Expected type String, but got " ++ show ctype1 ++ " at " ++ show pos]
             _ -> Right (S2BinaryOp CTBool "=" s2expr1 s2expr2)
getExprType parents varMappings classMappings selfName (S1Block _ exprs) =
        let s2exprs = map (getExprType parents varMappings classMappings selfName) exprs
            s2exprsValues = rights s2exprs
            errors = lefts s2exprs
        in if null errors
           then Right (S2Block (getType $ last s2exprsValues) s2exprsValues)
           else Left (concat errors)
getExprType parents varMappings classMappings selfName (S1If pos cond cexpr1 cexpr2) =
        do s2expr0 <- getExprType parents varMappings classMappings selfName cond
           s2expr1 <- getExprType parents varMappings classMappings selfName cexpr1
           s2expr2 <- getExprType parents varMappings classMappings selfName cexpr2
           let ctype0 = getType s2expr0
               ctype1 = getType s2expr1
               ctype2 = getType s2expr2
           if (ctype0 /= CTBool)
             then Left ["Expected type Bool, but got " ++ show ctype0 ++ " at " ++ show pos]
             else Right (S2If (getCommonAncestor parents [ctype1, ctype2]) s2expr0 s2expr1 s2expr2)
getExprType parents varMappings classMappings selfName (S1While pos cond cexpr) =
        do s2expr0 <- getExprType parents varMappings classMappings selfName cond
           s2expr1 <- getExprType parents varMappings classMappings selfName cexpr
           let ctype0 = getType s2expr0
           if ctype0 /= CTBool
             then Left ["Expected type Bool, but got " ++ show ctype0 ++ " at " ++ show pos]
             else Right (S2While CTObject s2expr0 s2expr1)
getExprType parents varMappings classMappings selfName (S1Let pos assigns cexpr) =
        getLetType varMappings [] assigns
        where getLetType varMappings' newAssigns [] = do s2expr <- getExprType parents varMappings' classMappings selfName cexpr
                                                         let ctype = getType s2expr
                                                         Right (S2Let ctype (reverse newAssigns) s2expr)
              getLetType varMappings' newAssigns ((varName, varTypeName, varExpr):t) = do varS2Expr <- getExprType parents varMappings' classMappings selfName varExpr
                                                                                          let varExprType = getType varS2Expr
                                                                                              varType = ctypeFromStringWithSelf selfName varTypeName
                                                                                          if isClass varType && Map.notMember varTypeName parents
                                                                                            then Left ["Unknown type: " ++ varTypeName ++ " at " ++ show pos]
                                                                                            else if varExpr /= S1Void && getCommonAncestor parents [varType, varExprType] /= varType
                                                                                            then Left ["Unconforms types: " ++ varTypeName ++ " and " ++ show varExprType ++ " at " ++ show pos]
                                                                                            else getLetType (Map.insert varName varType varMappings') ((varName, varTypeName, varS2Expr) : newAssigns) t
getExprType parents varMappings classMappings selfName (S1Case pos cexpr cases) =
        do s2expr <- getExprType parents varMappings classMappings selfName cexpr
           let ctype = getType s2expr
               names = map (\(name, _, _) -> name) cases
               ctypes = map (\(_, ctypeName, _) -> ctypeFromStringWithSelf selfName ctypeName) cases
               s2exprs = map (\(name, ctype', expr) -> getExprType parents (Map.insert name (ctypeFromString ctype') varMappings) classMappings selfName expr) cases
               unknownTypes = filter (\(CTClass name) -> Map.notMember name parents) $ filter isClass ctypes
               cexprErrors = lefts s2exprs
               s2exprsValues = rights s2exprs
               caseTypes = map getType s2exprsValues
               unconforms = filter (\ctype' -> let commonAncestor = getCommonAncestor parents [ctype, ctype'] in commonAncestor /= ctype && commonAncestor /= ctype') ctypes
               cmp CTObject CTObject = EQ
               cmp CTObject _ = GT
               cmp _ CTObject = LT
               cmp CTInt CTInt = EQ
               cmp CTBool CTBool = EQ
               cmp CTString CTString = EQ
               cmp (CTClass name1) (CTClass name2) = compare (length $ getAllParents parents name2) (length $ getAllParents parents name1)
               cmp _ _ = error "Error in comparsion of cases."
           if not $ null unknownTypes
             then Left (map (\(CTClass name) -> "Unknown type: " ++ name ++ " at " ++ show pos) unknownTypes)
             else if not $ null cexprErrors
             then Left (concat cexprErrors)
             else if not $ null unconforms
             then Left (map (\ctype' -> "Unconforms types: " ++ show ctype ++ " and " ++ show ctype' ++ " at " ++ show pos) unconforms)
             else Right (S2Case (getCommonAncestor parents caseTypes) s2expr (sortBy (\(_, ctype1, _) (_, ctype2, _) -> cmp ctype1 ctype2) $ zip3 names ctypes s2exprsValues))
getExprType parents varMappings classMappings selfName (S1Assign pos name cexpr) =
        if Map.notMember name varMappings
        then Left ["Unknown variable name: " ++ name ++ " at " ++ show pos]
        else do s2expr <- getExprType parents varMappings classMappings selfName cexpr
                let ctype = getType s2expr
                    varType = varMappings Map.! name
                if not $ isConforms parents ctype varType
                  then Left ["Unconforms types: " ++ show varType ++ " and " ++ show ctype ++ " at " ++ show pos]
                  else Right (S2Assign varType name s2expr)
getExprType _ _ _ _ _ = error "Error in semantics check."