module CIL where

import Semantics
import CodeGeneration

generateCIL :: (String -> String -> Maybe (CFuncResult, [CType])) -> CGProgram -> String
generateCIL classMappings program =
        let Just (mainResultType, _) = classMappings "Main" "main"
            mainResultType' = case mainResultType of
                                CRSelfType -> "Main"
                                CRType ctype -> ctypeToCIL ctype
        in ".assembly 'Cool' {}\n" ++
           "\n" ++
           ".class public auto ansi beforefieldinit __Main\n" ++
           "  extends [mscorlib]System.Object\n" ++
           "{\n" ++
           "  .method public static hidebysig\n" ++
           "    default void Main(string[] args) cil managed\n" ++
           "  {\n" ++
           "    .maxstack 8\n" ++
           "    .entrypoint\n" ++
           "    newobj instance void class Main::'.ctor'()\n" ++
           "    call instance " ++ mainResultType' ++ " Main::_main()\n" ++
           "    pop\n" ++
           "    ret\n" ++
           "  }\n" ++
           "}\n" ++
           "\n" ++
           ".class public auto ansi beforefieldinit __Object\n" ++
           "  extends [mscorlib]System.Object\n" ++
           "{\n" ++
           "  .method public static hidebysig\n" ++
           "    default object abort(object x) cil managed\n" ++
           "  {\n" ++
           "    .maxstack 8\n" ++
           "    ldc.i4.0\n" ++
           "    call void class [mscorlib]System.Environment::Exit(int32)\n" ++
           "    ldnull\n" ++
           "    ret\n" ++
           "  }\n" ++
           "  .method public static hidebysig\n" ++
           "    default object copy(object x) cil managed\n" ++
           "  {\n" ++
           "    .maxstack 8\n" ++
           "    ldarg.0\n" ++
           "    call instance object object::MemberwiseClone()\n" ++
           "    ret\n" ++
           "  }\n" ++
           "  .method public static hidebysig\n" ++
           "    default string type_name(object x) cil managed\n" ++
           "  {\n" ++
           "    .maxstack 8\n" ++
           "    ldarg.0\n" ++
           "    call instance class [mscorlib]System.Type object::GetType()\n" ++
           "    callvirt instance string class [mscorlib]System.Reflection.MemberInfo::get_Name()\n" ++
           "    ret\n" ++
           "  }\n" ++
           "}\n" ++
           "\n" ++
           ".class public auto ansi beforefieldinit IO\n" ++
           "  extends [mscorlib]System.Object\n" ++
           "{\n" ++
           "  .method public hidebysig specialname rtspecialname\n" ++
           "    instance default void '.ctor'() cil managed\n" ++
           "  {\n" ++
           "    .maxstack 8\n" ++
           "    ldarg.0\n" ++
           "    call instance void [mscorlib]System.Object::'.ctor'()\n" ++
           "    ret\n" ++
           "  }\n" ++
           "  .method public virtual hidebysig\n" ++
           "    instance default string _in_string() cil managed\n" ++
           "  {\n" ++
           "    .maxstack 8\n" ++
           "    call string class [mscorlib]System.Console::ReadLine()\n" ++
           "    ret\n" ++
           "  }\n" ++
           "  .method public virtual hidebysig\n" ++
           "    instance default class IO _out_string(string x) cil managed\n" ++
           "  {\n" ++
           "    .maxstack 8\n" ++
           "    ldarg.1\n" ++
           "    call void class [mscorlib]System.Console::Write(string)\n" ++
           "    ldarg.0\n" ++
           "    ret\n" ++
           "  }\n" ++
           "  .method public virtual hidebysig\n" ++
           "    instance default int32 _in_int() cil managed\n" ++
           "  {\n" ++
           "    .maxstack 8\n" ++
           "    call string class [mscorlib]System.Console::ReadLine()\n" ++
           "    call int32 int32::Parse(string)\n" ++
           "    ret\n" ++
           "  }\n" ++
           "  .method public virtual hidebysig\n" ++
           "    instance default class IO _out_int(int32 x) cil managed\n" ++
           "  {\n" ++
           "    .maxstack 8\n" ++
           "    ldarg.1\n" ++
           "    call void class [mscorlib]System.Console::Write(int32)\n" ++
           "    ldarg.0\n" ++
           "    ret\n" ++
           "  }\n" ++
           "}\n" ++
           "\n" ++
           concat (map classToCIL program)

classToCIL :: CGClass -> String
classToCIL (name, parent, fields, (ctorVars, ctorCmds, ctorStackSize), methods) =
        ".class public auto ansi beforefieldinit " ++ name ++ "\n" ++
        "  extends " ++ (if parent == "Object" then "[mscorlib]System.Object" else parent) ++ "\n" ++
        "{\n" ++
        concat (map fieldToCIL fields) ++
        "  .method public hidebysig specialname rtspecialname\n" ++
        "    instance default void '.ctor'() cil managed\n" ++
        "  {\n" ++
        "    .maxstack " ++ show (if ctorStackSize < 8 then 8 else ctorStackSize) ++ "\n" ++
        localsToCIL ctorVars ++
        concat (map commandToCIL ctorCmds) ++
        "  }\n" ++
        concat (map methodToCIL methods) ++
        "}\n" ++
        "\n"

fieldToCIL :: (CType, String) -> String
fieldToCIL (ctype, name) =
        "  .field public " ++ ctypeToCIL ctype ++ " " ++ convertName name ++ "\n"

methodToCIL :: CGMethod -> String
methodToCIL (name, ctype, args, vars, cmds, stackSize) =
        "  .method public virtual hidebysig\n" ++
        "    instance default " ++ ctypeToCIL ctype ++ " " ++ convertName name ++ "(" ++ argsToCIL args ++ ") cil managed\n" ++
        "  {\n" ++
        "    .maxstack " ++ show (if stackSize < 8 then 8 else stackSize) ++ "\n" ++
        localsToCIL vars ++
        concat (map commandToCIL cmds) ++
        "  }\n"

localsToCIL :: [(CType, String)] -> String
localsToCIL [] = ""
localsToCIL locals =
        "    .locals init (\n" ++
        localsToCIL' locals ++ ")\n"
        where localsToCIL' [] = ""
              localsToCIL' [(ctype, name)] = localsToCIL'' ctype name
              localsToCIL' ((ctype, name):t) = localsToCIL'' ctype name ++ ",\n" ++ localsToCIL' t
              localsToCIL'' ctype name = "      " ++ ctypeToCIL ctype ++ " " ++ convertName name

convertName :: String -> String
--convertName "char" = "_char"
--convertName "int" = "_int"
--convertName "bool" = "_bool"
--convertName "string" = "_string"
--convertName "object" = "_object"
--convertName "value" = "_value"
--convertName "init" = "_init"
--convertName "pop" = "_pop"
--convertName "out" = "_out"
--convertName "add" = "_add"
convertName name = '_' : name

argsToCIL :: [(CType, String)] -> String
argsToCIL [] = ""
argsToCIL [(ctype, name)] = ctypeToCIL ctype ++ " " ++ convertName name
argsToCIL ((ctype, name):t) = ctypeToCIL ctype ++ " " ++ convertName name ++ ", " ++ argsToCIL t

argsTypesToCIL :: [CType] -> String
argsTypesToCIL [] = ""
argsTypesToCIL [ctype] = ctypeToCIL ctype
argsTypesToCIL (ctype:t) = ctypeToCIL ctype ++ ", " ++ argsTypesToCIL t

ctypeToCIL :: CType -> String
ctypeToCIL CTObject = "[mscorlib]System.Object"
ctypeToCIL CTInt = "int32"
ctypeToCIL CTBool = "bool"
ctypeToCIL CTString = "string"
ctypeToCIL (CTClass name) = "class " ++ name

commandToCIL :: Command -> String
commandToCIL (Label l) = "   LABEL_" ++ show l ++ ":\n"
commandToCIL Add = "    add\n"
commandToCIL Sub = "    sub\n"
commandToCIL Mul = "    mul\n"
commandToCIL Div = "    div\n"
commandToCIL Ret = "    ret\n"
commandToCIL (Ldloc num) = if num <= 3
                           then "    ldloc." ++ show num ++ "\n"
                           else if num <= 255
                           then "    ldloc.s " ++ show num ++ "\n"
                           else "    ldloc " ++ show num ++ "\n"
commandToCIL (Ldarg num) = if num <= 3
                           then "    ldarg." ++ show num ++ "\n"
                           else if num <= 255
                           then "    ldarg.s " ++ show num ++ "\n"
                           else "    ldarg " ++ show num ++ "\n"
commandToCIL (Ldint val) = if val >= 0 && val <= 8
                           then "    ldc.i4." ++ show val ++ "\n"
                           else if val == -1
                           then "    ldc.i4.m1\n"
                           else if val >= -128 && val <= 127
                           then "    ldc.i4.s " ++ show val ++ "\n"
                           else "    ldc.i4 " ++ show val ++ "\n"
commandToCIL (Ldstr str) = "    ldstr " ++ show str ++ "\n"
commandToCIL (Ldfld ctype className fieldName) = "    ldfld " ++ ctypeToCIL ctype ++ " " ++ className ++ "::" ++ convertName fieldName ++ "\n"
commandToCIL (Stloc num) = if num <= 3
                           then "    stloc." ++ show num ++ "\n"
                           else if num <= 255
                           then "    stloc.s " ++ show num ++ "\n"
                           else "    stloc " ++ show num ++ "\n"
commandToCIL (Starg num) = if num <= 255
                           then "    starg.s " ++ show num ++ "\n"
                           else "    starg " ++ show num ++ "\n"
commandToCIL (Stfld ctype className fieldName) = "    stfld " ++ ctypeToCIL ctype ++ " " ++ className ++ "::" ++ convertName fieldName ++ "\n"
commandToCIL (Newobj "Object") = "    newobj instance void class [mscorlib]System.Object::'.ctor'()\n"
commandToCIL (Newobj name) = "    newobj instance void class " ++ name ++ "::'.ctor'()\n"
commandToCIL Ceq = "    ceq\n"
commandToCIL Ldnull = "    ldnull\n"
commandToCIL Neg = "    neg\n"
commandToCIL Clt = "    clt\n"
commandToCIL Cgt = "    cgt\n"
commandToCIL (Br l) = "    br LABEL_" ++ show l ++ "\n"
commandToCIL (Brfalse l) = "    brfalse LABEL_" ++ show l ++ "\n"
commandToCIL (Brtrue l) = "    brtrue LABEL_" ++ show l ++ "\n"
commandToCIL (Callctor name) = "    call instance void " ++ (if name == "Object" then "object" else name) ++ "::'.ctor'()\n"
commandToCIL Pop = "    pop\n"
commandToCIL (Callvirt CTInt "String" "length" []) = "    call instance int32 string::get_Length()\n"
commandToCIL (Callvirt CTString "String" "concat" [CTString]) = "    call string string::Concat(string, string)\n"
commandToCIL (Callvirt CTString "String" "substr" [CTInt, CTInt]) = "    call instance string string::Substring(int32, int32)\n"
commandToCIL (Callvirt CTObject "Object" "abort" []) = "    call object class __Object::abort(object)\n"
commandToCIL (Callvirt CTObject "Object" "copy" []) = "    call object class __Object::copy(object)\n"
commandToCIL (Callvirt CTString "Object" "type_name" []) = "    call string class __Object::type_name(object)\n"
commandToCIL (Call resultType className methodName args) = "    call instance " ++ ctypeToCIL resultType ++ " " ++ className ++ "::" ++ convertName methodName ++ "(" ++ argsTypesToCIL args ++ ")\n"
commandToCIL (Callvirt resultType className methodName args) = "    callvirt instance " ++ ctypeToCIL resultType ++ " " ++ className ++ "::" ++ convertName methodName ++ "(" ++ argsTypesToCIL args ++ ")\n"
commandToCIL Streq = "    call bool string::op_Equality(string, string)\n"
commandToCIL Boxint = "    box [mscorlib]System.Int32\n"
commandToCIL Boxbool = "    box [mscorlib]System.Boolean\n"
commandToCIL (Isinst CTObject) = "    isinst [mscorlib]System.Object\n"
commandToCIL (Isinst CTInt) = "    isinst [mscorlib]System.Int32\n"
commandToCIL (Isinst CTBool) = "    isinst [mscorlib]System.Boolean\n"
commandToCIL (Isinst CTString) = "    isinst [mscorlib]System.String\n"
commandToCIL (Isinst (CTClass name)) = "    isinst " ++ name ++ "\n"
commandToCIL Unboxint = "    unbox.any [mscorlib]System.Int32\n"
commandToCIL Unboxbool = "    unbox.any [mscorlib]System.Boolean\n"
commandToCIL (Throw msg) = "    ldstr " ++ show msg ++ "\n" ++
                           "    newobj instance void class [mscorlib]System.Exception::'.ctor'(string)\n" ++
                           "    throw\n"