module c

import v.ast
import v.util

const cprefix = 'v__reflection__'

// reflection_string maps string to its idx
fn (mut g Gen) reflection_string(str string) int {
	return unsafe {
		g.reflection_strings[str] or {
			g.reflection_strings[str] = g.reflection_strings.len
			g.reflection_strings.len - 1
		}
	}
}

// gen_reflection_strings generates the reflectino string registration
@[inline]
fn (mut g Gen) gen_reflection_strings() {
	for str, idx in g.reflection_strings {
		g.writeln('\t${cprefix}add_string(_SLIT("${str}"), ${idx});')
	}
}

// gen_empty_array generates code for empty array
@[inline]
fn (g &Gen) gen_empty_array(type_name string) string {
	return '__new_array_with_default(0, 0, sizeof(${type_name}), 0)'
}

// gen_functionarg_array generates the code for functionarg argument
@[inline]
fn (g &Gen) gen_functionarg_array(type_name string, node ast.Fn) string {
	if node.params.len == 0 {
		return g.gen_empty_array(type_name)
	}
	mut out := 'new_array_from_c_array(${node.params.len},${node.params.len},sizeof(${type_name}),'
	out += '_MOV((${type_name}[${node.params.len}]){'
	out += node.params.map('((${type_name}){.name=_SLIT("${it.name}"),.typ=${int(it.typ)},.is_mut=${it.is_mut}})').join(',')
	out += '}))'
	return out
}

// gen_functionarg_array generates the code for functionarg argument
@[inline]
fn (mut g Gen) gen_function_array(nodes []ast.Fn) string {
	type_name := '${cprefix}Function'

	if nodes.len == 0 {
		return g.gen_empty_array(type_name)
	}

	mut out := 'new_array_from_c_array(${nodes.len},${nodes.len},sizeof(${type_name}),'
	out += '_MOV((${type_name}[${nodes.len}]){'
	out += nodes.map(g.gen_reflection_fn(it)).join(',')
	out += '}))'
	return out
}

// gen_functionattr_array generates the code for functionarg attr
@[inline]
fn (g Gen) gen_functionattr_array(type_name string, node ast.Fn) string {
	if node.attrs.len == 0 {
		return g.gen_empty_array(type_name)
	}
	mut out := 'new_array_from_c_array(${node.attrs.len},${node.attrs.len},sizeof(${type_name}),'
	out += '_MOV((${type_name}[${node.attrs.len}]){'
	out += node.attrs.map('((${type_name}){.name=_SLIT("${it.name}"),.arg=_SLIT("${it.arg}"),.has_arg=${it.has_arg}})').join(',')
	out += '}))'
	return out
}

// gen_reflection_fn generates C code for Function struct
@[inline]
fn (mut g Gen) gen_reflection_fn(node ast.Fn) string {
	mut arg_str := '((${cprefix}Function){'
	v_name := node.name.all_after_last('.')
	arg_str += '.mod_name=_SLIT("${node.mod}"),'
	arg_str += '.name=_SLIT("${v_name}"),'
	arg_str += '.args=${g.gen_functionarg_array(cprefix + 'FunctionArg', node)},'
	arg_str += '.attrs=${g.gen_functionattr_array(cprefix + 'FnAttr', node)},'

	if !node.is_conditional && node.source_fn != 0 && 0 == node.generic_names.len && node.mod != '' && node.mod !in ['builtin','arrays'] && node.name.starts_with('${node.mod}.') {
		arg_str += '.fnptr=&${c_fn_name(node.name)},'
	}
	arg_str += '.file_idx=${g.reflection_string(util.cescaped_path(node.file))},'
	arg_str += '.line_start=${node.pos.line_nr},'
	arg_str += '.line_end=${node.pos.last_line},'
	arg_str += '.is_variadic=${node.is_variadic},'
	arg_str += '.return_typ=${int(node.return_type)},'
	arg_str += '.receiver_typ=${int(node.receiver_type)},'
	arg_str += '.is_pub=${node.is_pub}'
	arg_str += '})'
	return arg_str
}

// gen_reflection_sym generates C code for TypeSymbol struct
@[inline]
fn (mut g Gen) gen_reflection_sym(tsym ast.TypeSymbol) string {
	kind_name := tsym.kind.str()
	name := tsym.name.all_after_last('.')
	info := g.gen_reflection_sym_info(tsym)
	methods := g.gen_function_array(tsym.methods)
	return '(${cprefix}TypeSymbol){.name=_SLIT("${name}"),.mod=_SLIT("${tsym.mod}"),.idx=${tsym.idx},.parent_idx=${tsym.parent_idx},${g.get_type_size_offset(tsym)}.language=${cprefix}VLanguage__${tsym.language},.kind=${cprefix}VKind__${kind_name},.info=${info},.methods=${methods}}'
}

// gen_attrs_array generates C code for []Attr
@[inline]
fn (g &Gen) gen_attrs_array(attrs []ast.Attr) string {
	if attrs.len == 0 {
		return g.gen_empty_array('string')
	}
	mut out := 'new_array_from_c_array(${attrs.len},${attrs.len},sizeof(string),'
	out += '_MOV((string[${attrs.len}]){'
	out += attrs.map(if it.has_arg { '_SLIT("${it.name}=${it.arg}")' } else { '_SLIT("${it.name}")' }).join(',')
	out += '}))'
	return out
}

fn (g Gen) get_type_size_offset(type_symbol ast.TypeSymbol) string {
	mut result := ''
	mut size_ := 0
	mut align_ := 0
	if type_symbol.idx > 0 {
		size_,align_ = g.table.type_size(type_symbol.idx)
	}

	if type_symbol.language == ast.Language.c && type_symbol.info is ast.Struct{
		info := type_symbol.info as ast.Struct

		c_struct_name := if type_symbol.name in ['C.__stat64', 'C.DIR'] { //mac 没有__stat64结构, DIR比较异常
			''
		} else if _ := info.attrs.find_first('typedef') {
			type_symbol.name.replace_once('C.', '')
		}
		else {
			type_symbol.name.replace_once('C.', 'struct ')
		}

		result = if '' != c_struct_name {'.size=sizeof(${c_struct_name}),.align=__alignof(${c_struct_name}),'} else {''}

	} else {
		result = '.size=${size_},.align=${align_},'
	}

	return result
}

fn (g Gen) get_field_offset(in_type ast.Type, name string) string {
	mut result := '0'
	if in_type > 0 {
		type_symbol := g.table.sym(in_type)
		// if type_symbol.name.contains('TestStruct') {
		// 	println(type_symbol.debug())
		// }
		mut type_name := ''
		match type_symbol.language {
			.v {
				sym_name := if type_symbol.info is ast.Struct && type_symbol.info.scoped_name != '' {
					type_symbol.info.scoped_name
				} else {
					type_symbol.name
				}
				type_name = util.no_dots(sym_name)
			}
			.c {
				if type_symbol.info is ast.Struct {
					info := type_symbol.info as ast.Struct
					type_name = type_symbol.name.replace_once('C.', 'struct ')
					//mac 没有__stat64结构
					if type_symbol.name == 'C.__stat64' {
						''
					} else if _ := info.attrs.find_first('typedef') {
						type_name = type_symbol.name.replace_once('C.', '')
					}
				}
			}
			else {

			}
		}

		field_name := match type_symbol.language {
			.v {
				c_name(name)
			}
			else {
				util.no_dots(name)
			}
		}
		result = if '' != type_name { '__offsetof(${type_name},${field_name})' } else { '0' }
	}

	return result
}

// gen_fields_array generates C code for []StructField
@[inline]
fn (g &Gen) gen_fields_array(fields []ast.StructField) string {
	if fields.len == 0 {
		return g.gen_empty_array('${cprefix}StructField')
	}
	mut out := 'new_array_from_c_array(${fields.len},${fields.len},sizeof(${cprefix}StructField),'
	out += '_MOV((${cprefix}StructField[${fields.len}]){'
	out += fields.map('((${cprefix}StructField){.name=_SLIT("${it.name}"),.typ=${int(it.typ)},.attrs=${g.gen_attrs_array(it.attrs)},.is_pub=${it.is_pub},.is_mut=${it.is_mut},.offset=${g.get_field_offset(it.container_typ, it.name)}})').join(',')
	out += '}))'
	return out
}

// gen_type_array generates C code for []Type
@[inline]
fn (g &Gen) gen_type_array(types []ast.Type) string {
	if types.len == 0 {
		return g.gen_empty_array(ast.int_type_name)
	}
	return 'new_array_from_c_array(${types.len},${types.len},sizeof(${ast.int_type_name}),_MOV((int[${types.len}]){${types.map(int(it).str()).join(',')}}))'
}

// gen_string_array generates C code for []string
@[inline]
fn (g &Gen) gen_string_array(strs []string) string {
	if strs.len == 0 {
		return g.gen_empty_array('string')
	}
	items := strs.map('_SLIT("${it}")').join(',')
	return 'new_array_from_c_array(${strs.len},${strs.len},sizeof(string),_MOV((string[${strs.len}]){${items}}))'
}

// gen_reflection_sym_info generates C code for TypeSymbol's info sum type
@[inline]
fn (mut g Gen) gen_reflection_sym_info(tsym ast.TypeSymbol) string {
	match tsym.kind {
		.array {
			info := tsym.info as ast.Array
			s := 'ADDR(${cprefix}Array,(((${cprefix}Array){.nr_dims=${info.nr_dims},.elem_type=${int(info.elem_type)}})))'
			return '(${cprefix}TypeInfo){._${cprefix}Array = memdup(${s},sizeof(${cprefix}Array)),._typ=${g.table.find_type_idx('v.reflection.Array')}}'
		}
		.array_fixed {
			info := tsym.info as ast.ArrayFixed
			s := 'ADDR(${cprefix}ArrayFixed,(((${cprefix}ArrayFixed){.size=${info.size},.elem_type=${int(info.elem_type)}})))'
			return '(${cprefix}TypeInfo){._${cprefix}ArrayFixed=memdup(${s},sizeof(${cprefix}ArrayFixed)),._typ=${g.table.find_type_idx('v.reflection.ArrayFixed')}}'
		}
		.map {
			info := tsym.info as ast.Map
			s := 'ADDR(${cprefix}Map,(((${cprefix}Map){.key_type=${int(info.key_type)},.value_type=${int(info.value_type)}})))'
			return '(${cprefix}TypeInfo){._${cprefix}Map=memdup(${s},sizeof(${cprefix}Map)),._typ=${g.table.find_type_idx('v.reflection.Map')}}'
		}
		.sum_type {
			info := tsym.info as ast.SumType
			s := 'ADDR(${cprefix}SumType,(((${cprefix}SumType){.parent_idx=${info.parent_type.idx()},.variants=${g.gen_type_array(info.variants)}})))'
			return '(${cprefix}TypeInfo){._${cprefix}SumType=memdup(${s},sizeof(${cprefix}SumType)),._typ=${g.table.find_type_idx('v.reflection.SumType')}}'
		}
		.struct {
			info := tsym.info as ast.Struct
			attrs := g.gen_attrs_array(info.attrs)
			fields := g.gen_fields_array(info.fields)
			s := 'ADDR(${cprefix}Struct,(((${cprefix}Struct){.parent_idx=${(tsym.info as ast.Struct).parent_type.idx()},.attrs=${attrs},.fields=${fields}})))'
			return '(${cprefix}TypeInfo){._${cprefix}Struct=memdup(${s},sizeof(${cprefix}Struct)),._typ=${g.table.find_type_idx('v.reflection.Struct')}}'
		}
		.enum {
			info := tsym.info as ast.Enum
			vals := g.gen_string_array(info.vals)
			s := 'ADDR(${cprefix}Enum,(((${cprefix}Enum){.vals=${vals},.is_flag=${info.is_flag}})))'
			return '(${cprefix}TypeInfo){._${cprefix}Enum=memdup(${s},sizeof(${cprefix}Enum)),._typ=${g.table.find_type_idx('v.reflection.Enum')}}'
		}
		.function {
			info := tsym.info as ast.FnType
			s := 'ADDR(${cprefix}Function,${g.gen_reflection_fn(info.func)})'
			return '(${cprefix}TypeInfo){._${cprefix}Function=memdup(${s},sizeof(${cprefix}Function)),._typ=${g.table.find_type_idx('v.reflection.Function')}}'
		}
		.interface {
			name := tsym.name.all_after_last('.')
			info := tsym.info as ast.Interface
			methods := g.gen_function_array(info.methods)
			fields := g.gen_fields_array(info.fields)
			s := 'ADDR(${cprefix}Interface,(((${cprefix}Interface){.name=_SLIT("${name}"),.methods=${methods},.fields=${fields},.is_generic=${info.is_generic}})))'
			return '(${cprefix}TypeInfo){._${cprefix}Interface=memdup(${s},sizeof(${cprefix}Interface)),._typ=${g.table.find_type_idx('v.reflection.Interface')}}'
		}
		.alias {
			info := tsym.info as ast.Alias
			s := 'ADDR(${cprefix}Alias,(((${cprefix}Alias){.parent_idx=${info.parent_type.idx()},.language=${cprefix}VLanguage__${info.language.str()}})))'
			return '(${cprefix}TypeInfo){._${cprefix}Alias=memdup(${s},sizeof(${cprefix}Alias)),._typ=${g.table.find_type_idx('v.reflection.Alias')}}'
		}
		.multi_return {
			info := tsym.info as ast.MultiReturn
			s := 'ADDR(${cprefix}MultiReturn,(((${cprefix}MultiReturn){.types=${g.gen_type_array(info.types)}})))'
			return '(${cprefix}TypeInfo){._${cprefix}MultiReturn=memdup(${s},sizeof(${cprefix}MultiReturn)),._typ=${g.table.find_type_idx('v.reflection.MultiReturn')}}'
		}
		else {
			s := 'ADDR(${cprefix}None,(((${cprefix}None){.parent_idx=${tsym.parent_idx},})))'
			return '(${cprefix}TypeInfo){._${cprefix}None=memdup(${s},sizeof(${cprefix}None)),._typ=${g.table.find_type_idx('v.reflection.None')}}'
		}
	}
}

// gen_reflection_data generates code to initialized V reflection metadata
fn (mut g Gen) gen_reflection_data() {
	// modules declaration
	for mod_name in g.table.modules {
		g.writeln('\t${cprefix}add_module(_SLIT("${mod_name}"));')
	}

	// type symbols declaration
	for _, tsym in g.table.type_symbols {
		sym := g.gen_reflection_sym(tsym)
		g.writeln('\t${cprefix}add_type_symbol(${sym});')
	}

	// types declaration
	for full_name, idx in g.table.type_idxs {
		name := full_name.all_after_last('.')
		g.writeln('\t${cprefix}add_type((${cprefix}Type){.name=_SLIT("${name}"),.idx=${idx}});')
	}

	// func declaration (methods come from struct methods)
	for _, fn_ in g.table.fns {
		if fn_.no_body || fn_.is_method || fn_.language != .v {
			continue
		}
		func := g.gen_reflection_fn(fn_)
		g.writeln('\t${cprefix}add_func(${func});')
	}

	g.gen_reflection_strings()
}
