implementation module syntaxrepr

import syntax
from basic import listToString,showlist
import Heaprepr
import utilities

/* This module defines functions for converting (the contents of) data structures to string representation.
 */

instance toString AType
where toString at
      = toString at.at_annotation+++toString at.at_attribute+++toString at.at_type

instance toString ATypeVar
where toString atv
      = toString atv.atv_attribute+++toString atv.atv_annotation+++toString atv.atv_variable

instance toString App
where toString {app_symb, app_args, app_info_ptr}
      = "{app_symb = "+++toString app_symb+++
        ", app_args = "+++listToString app_args+++
        ", app_info_ptr = "+++toString app_info_ptr+++
        "}"

instance toString AttrInequality
where toString ai = toString ai.ai_offered+++" <= "+++toString ai.ai_demanded

instance toString BasicType
where
	toString BT_Int 		= "Int"
	toString BT_Char		= "Char"
	toString BT_Real		= "Real"
	toString BT_Bool		= "Bool"
	toString BT_Dynamic		= "Dynamic"
	toString BT_File		= "File"
	toString BT_World		= "World"
	toString (BT_String _)	= "String"

instance toString ClassDef
where toString {class_name, class_arity, class_args, class_context, class_members, class_dictionary, class_pos, class_cons_vars, class_arg_kinds}
      = "{class_name = "+++toString class_name+++
        ", class_arity = "+++toString class_arity+++
        ", class_args = "+++listToString class_args+++
        ", class_context = "+++listToString class_context+++
        ", class_members = "+++arrayToString class_members+++
        ", class_dictionary = "+++toString class_dictionary+++
        ", class_pos = "+++toString class_pos+++
        ", class_cons_vars = "+++toString class_cons_vars+++
        ", class_arg_kinds = "+++listToString class_arg_kinds+++
		"}"

instance toString ConsDef
where toString {cons_symb, cons_type, cons_arg_vars, cons_priority, cons_index, cons_type_index, cons_exi_vars, cons_type_ptr, cons_pos}
      = "{cons_symb = "+++toString cons_symb+++
		", cons_type = "+++toString cons_type+++
		", cons_arg_vars = "+++showlist listToString cons_arg_vars+++
		", cons_priority = "+++toString cons_priority+++
		", cons_index = "+++toString cons_index+++
		", cons_type_index = "+++toString cons_type_index+++
		", cons_exi_vars = "+++listToString cons_exi_vars+++
		", cons_type_ptr = "+++toString cons_type_ptr+++
		", cons_pos = "+++toString cons_pos+++
		"}"

instance toString ConsVariable
where toString (CV tv)       = "CV ("     +++toString tv +++")"
      toString (TempCV tvi)  = "TempCV (" +++toString tvi+++")"
      toString (TempQCV tvi) = "TempQCV ("+++toString tvi+++")"

instance toString DefinedSymbol
where toString {ds_ident, ds_arity, ds_index}
      = "{ds_ident = "+++toString ds_ident+++
        ", ds_arity = "+++toString ds_arity+++
        ", ds_index = "+++toString ds_index+++
		"}"

instance toString Expression
where toString _ = "<Expression>"

instance toString FieldSymbol
where toString {fs_name, fs_var, fs_index}
      = "{fs_name = "+++toString fs_name+++
	    ", fs_var = "+++toString fs_var+++
		", fs_index = "+++toString fs_index+++
		"}"

instance toString (Global a) | toString a
where toString {glob_module,glob_object} = toString glob_module+++"."+++toString glob_object

instance toString GlobalIndex
where toString {gi_module, gi_index} = "{gi_module = "+++toString gi_module+++", gi_index = "+++toString gi_index+++"}"

instance toString MemberDef
where toString {me_symb, me_class, me_offset, me_type, me_type_ptr, me_class_vars, me_pos, me_priority}
      = "{me_symb = "+++toString me_symb+++
        ", me_class = "+++toString me_class+++
        ", me_offset = "+++toString me_offset+++
        ", me_type = "+++toString me_type+++
        ", me_type_ptr = "+++toString me_type_ptr+++
        ", me_class_vars = "+++listToString me_class_vars+++
        ", me_pos = "+++toString me_pos+++
        ", me_priority = "+++toString me_priority+++
		"}"

instance toString Position
where toString (FunPos filename linenr funcname) = "FunPos "+++toString filename+++" "+++toString linenr+++" "+++toString funcname
      toString (LinePos filename linenr) = "LinePos "+++toString filename+++" "+++toString linenr
      toString (PreDefPos ident) = "PreDefPos "+++toString ident
      toString NoPos = "NoPos"

instance toString RecordType
where toString {rt_constructor, rt_fields} = "{rt_constructor = "+++toString rt_constructor+++", rt_fields = "+++arrayToString rt_fields+++"}"

instance toString SymbIdent
where toString {symb_name, symb_kind, symb_arity}
      = "{symb_name = "+++toString symb_name+++
        ", symb_kind = "+++toString symb_kind+++
        ", symb_arity = "+++toString symb_arity+++
        "}"

instance <<< SymbKind
where (<<<) file sk = file <<< toString sk

instance toString SymbKind
where toString SK_Unknown = "Unknown"
      toString (SK_Function gi) = "Function "+++toString gi
      toString (SK_LocalMacroFunction i) = "LocalMacroFunction "+++toString i
      toString (SK_OverloadedFunction gi) = "OverloadedFunction "+++toString gi
      toString (SK_Generic gi tk) = "Generic "+++toString gi+++" "+++toString tk
      toString (SK_Constructor gi) = "Constructor "+++toString gi
      toString (SK_Macro gi) = "Macro "+++toString gi
      toString (SK_GeneratedFunction fip i) = "GeneratedFunction "+++toString fip+++" "+++toString i
      toString SK_TypeCode = "TypeCode"

instance toString SelectorDef
where toString {sd_symb, sd_field, sd_type, sd_exi_vars, sd_field_nr, sd_type_index, sd_type_ptr, sd_pos}
      = "{sd_symb = "+++toString sd_symb+++
        ", sd_field = "+++toString sd_field+++
        ", sd_type = "+++toString sd_type+++
        ", sd_exi_vars = "+++listToString sd_exi_vars+++
        ", sd_field_nr = "+++toString sd_field_nr+++
        ", sd_type_index = "+++toString sd_type_index+++
        ", sd_type_ptr = "+++toString sd_type_ptr+++
        ", sd_pos = "+++toString sd_pos+++
		"}"

instance toString SymbolType
where toString st
      = "{st_vars = "+++listToString st.st_vars+++
	    ", st_args = "+++listToString st.st_args+++
	    ", st_arity = "+++toString st.st_arity+++
	    ", st_result = "+++toString st.st_result+++
	    ", st_context = "+++listToString st.st_context+++
	    ", st_attr_vars = "+++listToString st.st_attr_vars+++
	    ", st_attr_env = "+++listToString st.st_attr_env+++
		"}"

instance toString Type
where toString (TA tsident argtypes)
      = "("+++toString tsident+++foldr prependtype ")" argtypes
      toString (argtype --> restype) = "("+++toString argtype+++" -> "+++toString restype+++")"
      toString (TArrow) = "(->)"
      toString (TArrow1	argtype) = "("+++toString argtype+++" ->)"
      toString (tconsvar :@: argtypes) = "("+++toString tconsvar+++foldr prependtype ")" argtypes
      toString (TB bt) = "<BT "+++toString bt+++">"
      toString (TFA newtypevars type) = "A."+++listToString newtypevars+++"."+++toString type
      toString (GTV typevar) = "<GTV "+++toString typevar+++">"
      toString (TV typevar) = toString typevar
      toString (TempV tvid) = "<TempV "+++toString tvid+++">"
      toString (TQV	typevar) = "<TQV "+++toString typevar+++">"
      toString (TempQV tvid) = "<TempQV "+++toString tvid+++">"
      toString (TLifted typevar) = "<TLifted "+++toString typevar+++">"
      toString (TE) = "<TE>"
prependtype argtype rest = " "+++toString argtype+++rest

instance toString TypeContext
where toString tc = toString tc.tc_class+++" "+++listToString tc.tc_types+++" "+++toString tc.tc_var

instance toString TypeDef a | toString a
where toString {td_name, td_index, td_arity, td_args, td_attrs, td_context, td_rhs, td_attribute, td_pos, td_used_types}
      = "{td_name = "+++toString td_name+++
		", td_index = "+++toString td_index+++
		", td_arity = "+++toString td_arity+++
		", td_args = "+++listToString td_args+++
		", td_attrs = "+++listToString td_attrs+++
		", td_context = "+++listToString td_context+++
		", td_rhs = "+++toString td_rhs+++
		", td_attribute = "+++toString td_attribute+++
		", td_pos = "+++toString td_pos+++
		", td_used_types = "+++listToString td_used_types+++
		"}"

instance toString TypeRhs
where toString (AlgType dss) = "AlgType "+++listToString dss
      toString (SynType at) = "SynType "+++toString at
	  toString (RecordType rt) = "RecordType "+++toString rt
	  toString (AbstractType bv) = "AbstractType "+++toString bv
	  toString (UnknownType) = "UnknownType"

instance toString TypeSymbIdent
where toString tsi = toString tsi.type_name+++"/"+++toString tsi.type_arity+++"@"+++toString tsi.type_index

//arrayToString :: .{a} -> String | toString a
//arrayToString :: .(a b) -> {#Char} | Array .a & select_u , size_u , toString b;
arrayToString row
= repr+++"}"
  where (_,repr) = iFoldSt convelem 0 (size row) ("{", "")
        convelem i (prefix, repr) = (",", repr+++prefix+++toString row.[i])

instance toString TypeVar
where toString tv = toString tv.tv_info_ptr
