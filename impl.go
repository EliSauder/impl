// impl generates method stubs for implementing an interface.
package main

import (
	"bytes"
	"errors"
	"flag"
	"fmt"
	"go/ast"
	"go/build"
	"go/format"
	"go/parser"
	"go/printer"
	"go/token"
	"os"
	"path/filepath"
	"slices"
	"strconv"
	"strings"
	"text/template"
	"unicode"

	"golang.org/x/tools/imports"
)

var (
	flagSrcDir   = flag.String("dir", "", "package source directory, useful for vendored code")
	flagComments = flag.Bool("comments", true, "include interface comments in the generated stubs")
	flagRecvPkg  = flag.String("recvpkg", "", "package name of the receiver")
)

// Type is a parsed type reference.
type Type struct {
	// Name is the type's name. For example, in "foo[Bar, Baz]", the name
	// is "foo".
	Name string

	// Params are the type's type params. For example, in "foo[Bar, Baz]",
	// the Params are []string{"Bar", "Baz"}.
	//
	// Params never list the type of the "name type" construction of type
	// params used when defining a generic type. They will always be just
	// the filling type, as seen when using a generic type.
	//
	// Params will always be the type parameters only for the top-level
	// type; if the params themselves have type parameters, they will
	// remain joined to the type name. So "foo[Bar, Baz[Quux]]" will be
	// returned as {ID: "foo", Params: []string{"Bar", "Baz[Quux]"}}
	Params []string
}

type Path struct {
	Path string
	Alias string
}

type PathType struct {
	Type []rune
	Module []rune
	Path []rune
	ModuleIsAlias bool
	qualifiedType []rune
	pathQualifiedType []rune
	packageImport []rune
}

func (pt *PathType) GetPath() Path {
	if pt.ModuleIsAlias {
		return Path{
			Path: string(pt.Path),
			Alias: string(pt.Module),
		}
	}
	return Path {
		Path: string(pt.Path),
	}
}

func (pt *PathType) PackageImport() []rune {
	if len(pt.Path) == 0 {
		return []rune{}
	}

	if len(pt.pathQualifiedType) > 0 {
		return pt.packageImport
	}

	pt.packageImport = append(pt.packageImport, []rune("import ")...)
	if pt.ModuleIsAlias {
		pt.packageImport = append(pt.packageImport, pt.Module...)
		pt.packageImport = append(pt.packageImport, []rune(" ")...)
	}
	pt.packageImport = append(pt.packageImport, []rune("\"")...)
	pt.packageImport = append(pt.packageImport, pt.Path...)
	pt.packageImport = append(pt.packageImport, []rune("\"")...)

	return pt.packageImport
}

func (pt *PathType) PathQualifiedType() []rune {
	if len(pt.pathQualifiedType) > 0 {
		return pt.pathQualifiedType
	}

	if len(pt.Path) > 0 {
		pt.pathQualifiedType = append(pt.pathQualifiedType, '"')
		pt.pathQualifiedType = append(pt.pathQualifiedType, pt.Path...)
		if pt.ModuleIsAlias {
			pt.pathQualifiedType = append(pt.pathQualifiedType, ';')
			pt.pathQualifiedType = append(pt.pathQualifiedType, pt.Module...)
		}
		pt.pathQualifiedType = append(pt.pathQualifiedType, '"', '.')
	}
	pt.pathQualifiedType = append(pt.pathQualifiedType, pt.Type...)

	return pt.pathQualifiedType
}

func (pt *PathType) ModuleQualifiedType() []rune {
	if len(pt.Module) == 0 {
		return pt.Type
	}
	if len(pt.qualifiedType) > 0 {
		return pt.qualifiedType
	}
	pt.qualifiedType = append(pt.qualifiedType, pt.Module...)
	pt.qualifiedType = append(pt.qualifiedType, '.')
	pt.qualifiedType = append(pt.qualifiedType, pt.Type...)

	return pt.qualifiedType
}

// String constructs a reference to the Type. For example:
// Type{Name: "Foo", Params{"Bar", "Baz[[]Quux]"}}
// would yield
// Foo[Bar, Baz[[]Quux]]
func (t Type) String() string {
	if len(t.Params) < 1 {
		return t.Name
	}
	return t.Name + "[" + strings.Join(t.Params, ", ") + "]"
}

// parseType parses an interface reference into a Type, allowing us to
// distinguish between the interface's name and its type parameters.
func parseType(in string) (Type, error) {
	expr, err := parser.ParseExpr(in)
	if err != nil {
		return Type{}, err
	}
	return typeFromAST(expr)
}

// stripPaths converts full package paths to short qualified names.
// It identifies path-like segments (sequences of Unicode letters, digits,
// underscores, dots, and slashes) and strips everything up to and including
// the last slash in each segment.
//
// Examples:
//
//	"Iface[github.com/foo/bar.T]" -> "Iface[bar.T]"
//	"Iface[a/b.T, c/d.U]" -> "Iface[b.T, d.U]"
//	"Iface[a/b.Other[c/d.T]]" -> "Iface[b.Other[d.T]]"
//	"Iface[*a/b.T]" -> "Iface[*b.T]"
// For more examples, see the tests in impl_test.go
//
// Because of the staggered parsing, the handling of quoted paths is done in
// a way that supports seeing the start and end quote in separate loop
// iterations.
//
// Algorithm Example:
// Given: "github.com/foo".Iface
//
// 1. First iteration
//   a. Grab all path characters (none, because " is first)
//   b. Grab all non-path characters (")
//   c. Strip quotes (remove only the one)
// 2. Second iteration
//   a. Grab all path characters (github.com/foo)
//   b. Grab all non-path characters (")
//   c. Strip second quote
// 3. etc
func stripPaths(in string) (string, []PathType, error) {
	remain := []rune(in)
	out := make([]rune, 0, len(remain))
	pts := []PathType{}

	for len(remain) > 0 {
		var pt PathType
		var seg []rune
		var more bool
		var err error

		pt, remain, more, err = getPathSeg(remain)
		if err != nil {
			return "", []PathType{}, err
		}
		out = append(out, pt.ModuleQualifiedType()...)
		if string(pt.Type) != "map" || len(pt.Module) != 0 {
			pts = append(pts, pt)
		}
		if !more {
			break
		}

		seg, remain, more = getNonPathSeg(remain)
		out = append(out, seg...)
		if !more {
			break
		}
	}

	for _, pt := range pts {
		fmt.Printf("id: %s\r\n\timport: %s\r\n\ttype: %s\r\n", string(out), string(pt.PackageImport()), string(pt.PathQualifiedType()))
	}

	return string(out), pts, nil
}

func getNonPathSeg(runes []rune)  (seg []rune, remain []rune, more bool) {
	// Get index of next path character
	n := slices.IndexFunc(runes, isQuotedAliasPathString)
	// Copy all characters before the path character
	seg = runes
	if n >= 0 {
		seg = seg[:n]
	}
	// If there are no path like characters, we are done
	if n == -1 {
		return seg, []rune{}, false
	}
	remain = runes[n:]
	return seg, remain, true
}

func getPathSeg(runes []rune) (pt PathType, remain []rune, more bool, err error) {
	// Find first index of a non-path character
	n := slices.IndexFunc(runes, isNotQuotedAliasPathString)
	// Get characters up to the non-path character
	seg := runes
	if n >= 0 {
		seg = seg[:n]
	}
	pt, err = parsePathAndType(seg)
	if err != nil {
		return pt, []rune{}, false, err
	}

	// if there is no non-path like characters, we are done
	if n == -1 {
		return pt, []rune{}, false, nil
	}
	remain = runes[n:]
	return pt, remain, true, nil
}

func parsePathAndType(seg []rune) (PathType, error) {
	if len(seg) == 0 {
		return PathType{}, errors.New("expected content in segment")
	}

	loc, err := pathRuneLocations(seg)
	if err != nil {
		return PathType{}, err
	}

	hasModule := loc.typeQualifierRune >= 0
	hasPath := loc.lastPathSegRune >= 0
	hasAlias := loc.aliasSegRune >= 0

	typeStart := loc.typeQualifierRune + 1

	moduleStart := max(loc.aliasSegRune, loc.lastPathSegRune, loc.firstQuote) + 1
	moduleEnd := useInOrder(loc.lastQuote, loc.typeQualifierRune)

	pathStart := loc.firstQuote + 1
	pathEnd := useInOrder(loc.aliasSegRune, loc.lastQuote, loc.typeQualifierRune)


	var typ []rune = seg[typeStart:]
	var mod []rune
	var path []rune

	if hasModule {
		mod = seg[moduleStart:moduleEnd]
	}
	if hasPath {
		path = seg[pathStart:pathEnd]
	}

	return PathType{
		Type: typ,
		Module: mod,
		Path: path,
		ModuleIsAlias: hasAlias,
	}, nil
}

type pathDetails struct {
	lastPathSegRune int
	aliasSegRune int
	typeQualifierRune int
	firstQuote int
	lastQuote int
}

func pathRuneLocations(seg []rune) (pathDetails, error) {
	if len(seg) == 0{
		return pathDetails{}, errors.New("no segment to read for path or type")
	}
	lastPathSeg := -1
	typeQualifierRune := -1
	aliasSegRune := -1
	firstQuote := -1
	lastQuote := -1
	numQuotes := 0

	for i, r := range seg {
		switch r {
		case '/':
			lastPathSeg = i
		case '.':
			typeQualifierRune = i
		case '"':
			numQuotes += 1
			if firstQuote == -1 {
				firstQuote = i
			}
			lastQuote = i
		case ';':
			if aliasSegRune != -1 {
				return pathDetails{}, errors.New("unexpected second alias")
			}
			aliasSegRune = i
		}
	}
	if typeQualifierRune == len(seg) - 1 {
		return pathDetails{}, errors.New("no type provided in path")
	}
	if numQuotes != 0 && numQuotes != 2 {
		return pathDetails{}, errors.New("unexpected number of quotes, expected 0 or 2")
	}
	if typeQualifierRune < 0 && lastPathSeg > 0 {
		return pathDetails{}, errors.New("type must be qualified when providing its path")
	}
	// type qualifier should not be between quotes and should be after the
	// last path separator
	if (lastQuote > 0 && typeQualifierRune != lastQuote + 1) ||
		typeQualifierRune < lastPathSeg {
		return pathDetails{}, errors.New("expected type qualifier after path")
	}

	if numQuotes > 0 && firstQuote != 0 {
		return pathDetails{}, errors.New("when using quoted paths, quote must start path")
	}

	return pathDetails{
		lastPathSegRune: lastPathSeg,
		aliasSegRune: aliasSegRune,
		typeQualifierRune: typeQualifierRune,
		firstQuote: firstQuote,
		lastQuote: lastQuote,
	}, nil
}


func useInOrder(vals ...int) int {
	for _, val := range vals {
		if val >= 0 {
			return val
		}
	}
	return vals[len(vals)-1]
}

func checkForQuote(p []rune) bool {
	if len(p) == 0 {
		return false
	}
	return p[0] == '"' || p[len(p)-1] == '"'
}

func trimPathSeg(p []rune) []rune {
	if len(p) == 0 {
		return p
	}

	if p[0] == '"' {
		return p[1:]
	}

	if p[len(p)-1] == '"' {
		return p[:len(p)-1]
	}

	return p
}

// lastIndex returns the index of the last occurrence of v in s, or -1 if not present.
func lastIndex[S ~[]E, E comparable](s S, v E) int {
	for i := len(s) - 1; i >= 0; i-- {
		if s[i] == v {
			return i
		}
	}
	return -1
}

// isPathRune reports whether r can appear in an import path.
// See https://go.dev/ref/spec#Import_declarations.
func isPathRune(r rune) bool {
	return unicode.IsPrint(r) && !strings.ContainsRune(" \uFFFD!\"#$%&'()*,:;<=>?[\\]^`{|}", r)
}

func isQuotedAliasPathString(r rune) bool {
	return isPathRune(r) || r == '"' || r == ';'
}

func isNotQuotedAliasPathString(r rune) bool {
	return !isQuotedAliasPathString(r)
}

func isPathTerminatingCharacter(r rune) bool {
	return strings.ContainsRune("=!?: \uFFFD", r)
}

func isNonPathRune(r rune) bool {
	return !isPathRune(r)
}

// findInterface returns the import path and type of an interface.
// For example, given "http.ResponseWriter", findInterface returns
// "net/http", Type{Name: "ResponseWriter"}.
// If a fully qualified interface is given, such as "net/http.ResponseWriter",
// it simply parses the input.
// If an unqualified interface such as "UserDefinedInterface" is given, then
// the interface definition is presumed to be in the package within srcDir and
// findInterface returns "", Type{Name: "UserDefinedInterface"}.
//
// Generic types will have their type params set in the Params property of
// the Type. Input should always reference generic types with their parameters
// specified: GenericType[string, bool], not GenericType[A any, B comparable].
func findInterface(input string, srcDir string) ([]Path, Type, error) {
	if len(strings.Fields(input)) != 1 && !strings.Contains(input, "[") {
		return []Path{}, Type{}, fmt.Errorf("couldn't parse interface: %s", input)
	}

	srcPath := filepath.Join(srcDir, "__go_impl__.go")

	// Find the base type (without generic params) to extract package path.
	// This handles cases like: pkg.Interface[other/pkg.Type]
	//baseInput := input
	//if bracket := strings.Index(input, "["); bracket > -1 {
	//	baseInput = input[:bracket]
	//}

	id, pts, err := stripPaths(input)
	if err != nil {
		return []Path{}, Type{}, err
	}
	iface, err := parseType(id)
	if err != nil {
		return []Path{}, Type{}, err
	}

	paths := make([]Path, 0, len(pts))

	countWithoutPath := 0

	for _, pt := range pts {
		if len(pt.Path) != 0 {
			paths = append(paths, pt.GetPath())
			continue
		}
		countWithoutPath++
	}

	if countWithoutPath == 0 {
		return paths, iface, nil
	}

	iface, paths, err = autoMagicImport(id, srcPath, paths)
	if err != nil {
		return []Path{}, Type{}, err
	}

	return paths, iface, nil

}

func autoMagicImport(typ string, srcPath string, paths []Path) (Type, []Path, error) {
	src := []byte("package automagicimport\nimport (")
	for _, p := range paths {
		src = append(src, '"')
		src = append(src, p.Path...)
		src = append(src, "\"\n"...)
	}
	src = append(src, ([]byte(")\nvar i " + typ))...)

	imp, err := imports.Process(srcPath, src, nil)
	if err != nil {
		return Type{}, []Path{}, err
	}

	fset := token.NewFileSet()
	f, err := parser.ParseFile(fset, srcPath, imp, 0)
	if err != nil {
		return Type{}, []Path{}, err
	}

	qualified := strings.Contains(typ, ".")

	if len(f.Imports) == 0 && qualified {
		return Type{}, []Path{}, fmt.Errorf("unrecognized type: %s", typ)
	}

	paths = make([]Path, 0, len(paths))

	for _, i := range f.Imports {
		imp := i.Path.Value
		imp, err := strconv.Unquote(imp)
		if err != nil {
			return Type{}, []Path{}, err
		}
		paths = append(paths, Path{Path:imp})
	}

	decl := f.Decls[len(f.Decls)-1].(*ast.GenDecl)
	spec := decl.Specs[0].(*ast.ValueSpec) 	// i <type>

	iface, err := typeFromAST(spec.Type)
	if err != nil {
		return Type{}, []Path{}, err
	}

	_, iface.Name, _ = strings.Cut(iface.Name, ".")

	return iface, paths, err
}

func typeFromAST(in ast.Expr) (Type, error) {
	// Extract type name and params from generic types.
	var typeName ast.Expr
	var typeParams []ast.Expr
	switch in := in.(type) {
	case *ast.IndexExpr:
		// a generic type with one type parameter (Reader[Foo]) shows up as an IndexExpr
		typeName = in.X
		typeParams = []ast.Expr{in.Index}
	case *ast.IndexListExpr:
		// a generic type with multiple type parameters shows up as an IndexListExpr
		typeName = in.X
		typeParams = in.Indices
	}
	if typeParams != nil {
		id, err := typeFromAST(typeName)
		if err != nil {
			return Type{}, err
		}
		if len(id.Params) > 0 {
			return Type{}, fmt.Errorf("unexpected type parameters: %v", in)
		}
		res := Type{Name: id.Name}
		for _, typeParam := range typeParams {
			param, err := typeFromAST(typeParam)
			if err != nil {
				return Type{}, err
			}
			res.Params = append(res.Params, param.String())
		}
		return res, nil
	}
	// Non-generic type.
	buf := new(strings.Builder)
	err := format.Node(buf, token.NewFileSet(), in)
	if err != nil {
		return Type{}, err
	}
	return Type{Name: buf.String()}, nil
}

// Pkg is a parsed build.Package.
type Pkg struct {
	*build.Package
	*token.FileSet
	// recvPkg is the package name of the function receiver
	recvPkg string
}

// Spec is ast.TypeSpec with the associated comment map.
type Spec struct {
	*ast.TypeSpec
	ast.CommentMap
	TypeParams map[string]string
}

// typeSpec locates the *ast.TypeSpec for type id in the import path.
func typeSpec(path string, typ Type, srcDir string) (Pkg, Spec, error) {
	var pkg *build.Package
	var err error

	if path == "" {
		pkg, err = build.ImportDir(srcDir, 0)
		if err != nil {
			return Pkg{}, Spec{}, fmt.Errorf("couldn't find package in %s: %v", srcDir, err)
		}
	} else {
		pkg, err = build.Import(path, srcDir, 0)
		if err != nil {
			return Pkg{}, Spec{}, fmt.Errorf("couldn't find package %s: %v", path, err)
		}
	}

	fset := token.NewFileSet() // share one fset across the whole package
	var files []string
	files = append(files, pkg.GoFiles...)
	files = append(files, pkg.CgoFiles...)
	for _, file := range files {
		f, err := parser.ParseFile(fset, filepath.Join(pkg.Dir, file), nil, parser.ParseComments)
		if err != nil {
			continue
		}

		for _, decl := range f.Decls {
			decl, ok := decl.(*ast.GenDecl)
			if !ok || decl.Tok != token.TYPE {
				continue
			}
			for _, spec := range decl.Specs {
				spec := spec.(*ast.TypeSpec)
				if spec.Name.Name != typ.Name {
					continue
				}
				typeParams, ok := matchTypeParams(spec, typ.Params)
				if !ok {
					continue
				}
				p := Pkg{Package: pkg, FileSet: fset}
				s := Spec{TypeSpec: spec, TypeParams: typeParams}
				return p, s, nil
			}
		}
	}
	return Pkg{}, Spec{}, fmt.Errorf("type %s not found in %s", typ.Name, path)
}

// matchTypeParams returns a map of type parameters from a parsed interface
// definition and the types that fill them from the user's specified type
// info. If the passed params can't be used to fill the type parameters on the
// passed type, a nil map and false are returned. No type checking is done,
// only that there are sufficient types to match.
func matchTypeParams(spec *ast.TypeSpec, params []string) (map[string]string, bool) {
	if spec.TypeParams == nil {
		return nil, true
	}
	res := make(map[string]string, len(params))
	var specParamNames []string
	for _, typeParam := range spec.TypeParams.List {
		for _, name := range typeParam.Names {
			if name == nil {
				continue
			}
			specParamNames = append(specParamNames, name.Name)
		}
	}
	if len(specParamNames) != len(params) {
		return nil, false
	}
	for pos, specParamName := range specParamNames {
		res[specParamName] = params[pos]
	}
	return res, true
}

// gofmt pretty-prints e.
func (p Pkg) gofmt(e ast.Expr) string {
	var buf bytes.Buffer
	printer.Fprint(&buf, p.FileSet, e)
	return buf.String()
}

// fullType returns the fully qualified type of e.
// Examples, assuming package net/http:
//
//	fullType(int) => "int"
//	fullType(Handler) => "http.Handler"
//	fullType(io.Reader) => "io.Reader"
//	fullType(*Request) => "*http.Request"
func (p Pkg) fullType(e ast.Expr) string {
	ast.Inspect(e, func(n ast.Node) bool {
		switch n := n.(type) {
		case *ast.Ident:
			// Using typeSpec instead of IsExported here would be
			// more accurate, but it'd be crazy expensive, and if
			// the type isn't exported, there's no point trying
			// to implement it anyway.
			if n.IsExported() && p.recvPkg != p.Package.Name {
				n.Name = p.Package.Name + "." + n.Name
			}
		case *ast.SelectorExpr:
			return false
		}
		return true
	})
	return p.gofmt(e)
}

func (p Pkg) params(field *ast.Field, typeParams map[string]string) []Param {
	var params []Param
	var typ string
	switch expr := field.Type.(type) {
	case *ast.Ident:
		if genType, ok := typeParams[expr.Name]; ok {
			typ = genType
		} else {
			typ = p.fullType(field.Type)
		}
	default:
		typ = p.fullType(field.Type)
	}
	for _, name := range field.Names {
		params = append(params, Param{Name: name.Name, Type: typ})
	}
	// Handle anonymous params
	if len(params) == 0 {
		params = []Param{{Type: typ}}
	}
	return params
}

// Method represents a method signature.
type Method struct {
	Recv string
	Func
}

// Func represents a function signature.
type Func struct {
	Name     string
	Params   []Param
	Res      []Param
	Comments string
}

// Param represents a parameter in a function or method signature.
type Param struct {
	Name string
	Type string
}

// EmitComments specifies whether comments from the interface should be preserved in the implementation.
type EmitComments bool

const (
	WithComments    EmitComments = true
	WithoutComments EmitComments = false
)

func (p Pkg) funcsig(f *ast.Field, typeParams map[string]string, cmap ast.CommentMap, comments EmitComments) Func {
	fn := Func{Name: f.Names[0].Name}
	typ := f.Type.(*ast.FuncType)
	if typ.Params != nil {
		for _, field := range typ.Params.List {
			for _, param := range p.params(field, typeParams) {
				// only for method parameters:
				// assign a blank identifier "_" to an anonymous parameter
				if param.Name == "" {
					param.Name = "_"
				}
				fn.Params = append(fn.Params, param)
			}
		}
	}
	if typ.Results != nil {
		for _, field := range typ.Results.List {
			fn.Res = append(fn.Res, p.params(field, typeParams)...)
		}
	}
	if comments == WithComments && f.Doc != nil {
		fn.Comments = flattenDocComment(f)
	}
	return fn
}

// The error interface is built-in.
var errorInterface = []Func{{
	Name: "Error",
	Res:  []Param{{Type: "string"}},
}}

// funcs returns the set of methods required to implement iface.
// It is called funcs rather than methods because the
// function descriptions are functions; there is no receiver.
func funcs(iface, srcDir, recvPkg string, comments EmitComments) ([]Func, error) {
	// Special case for the built-in error interface.
	if iface == "error" {
		return errorInterface, nil
	}

	// Locate the interface.
	path, typ, err := findInterface(iface, srcDir)
	if err != nil {
		return nil, err
	}

	// Parse the package and find the interface declaration.
	p, spec, err := typeSpec(path[0].Path, typ, srcDir)
	if err != nil {
		return nil, fmt.Errorf("interface %s not found: %s", iface, err)
	}
	p.recvPkg = recvPkg

	idecl, ok := spec.Type.(*ast.InterfaceType)
	if !ok {
		return nil, fmt.Errorf("not an interface: %s", iface)
	}

	if idecl.Methods == nil {
		return nil, fmt.Errorf("empty interface: %s", iface)
	}

	var fns []Func
	for _, fndecl := range idecl.Methods.List {
		if len(fndecl.Names) == 0 {
			// Embedded interface: recurse
			embedded, err := funcs(p.fullType(fndecl.Type), srcDir, recvPkg, comments)
			if err != nil {
				return nil, err
			}
			fns = append(fns, embedded...)
			continue
		}

		fn := p.funcsig(fndecl, spec.TypeParams, spec.CommentMap.Filter(fndecl), comments)
		fns = append(fns, fn)
	}
	return fns, nil
}

const stub = "{{if .Comments}}{{.Comments}}{{end}}" +
	"func ({{.Recv}}) {{.Name}}" +
	"({{range .Params}}{{.Name}} {{.Type}}, {{end}})" +
	"({{range .Res}}{{.Name}} {{.Type}}, {{end}})" +
	"{\n" + "panic(\"not implemented\") // TODO: Implement" + "\n}\n\n"

var tmpl = template.Must(template.New("test").Parse(stub))

// genStubs prints nicely formatted method stubs
// for fns using receiver expression recv.
// If recv is not a valid receiver expression,
// genStubs will panic.
// genStubs won't generate stubs for
// already implemented methods of receiver.
func genStubs(recv string, fns []Func, implemented map[string]bool) []byte {
	var recvName string
	if recvs := strings.Fields(recv); len(recvs) > 1 {
		recvName = recvs[0]
	}

	// (r *recv) F(r string) {} => (r *recv) F(_ string)
	fixParams := func(params []Param) {
		for i, p := range params {
			if p.Name == recvName {
				params[i].Name = "_"
			}
		}
	}

	buf := new(bytes.Buffer)
	for _, fn := range fns {
		if implemented[fn.Name] {
			continue
		}

		fixParams(fn.Params)
		fixParams(fn.Res)
		meth := Method{Recv: recv, Func: fn}
		tmpl.Execute(buf, meth)
	}

	pretty, err := format.Source(buf.Bytes())
	if err != nil {
		panic(err)
	}
	return pretty
}

// validReceiver reports whether recv is a valid receiver expression.
func validReceiver(recv string) bool {
	if recv == "" {
		// The parse will parse empty receivers, but we don't want to accept them,
		// since it won't generate a usable code snippet.
		return false
	}
	fset := token.NewFileSet()
	_, err := parser.ParseFile(fset, "", "package hack\nfunc ("+recv+") Foo()", 0)
	return err == nil
}

// flattenDocComment flattens the field doc comments to a string
func flattenDocComment(f *ast.Field) string {
	var result strings.Builder
	for _, c := range f.Doc.List {
		result.WriteString(c.Text)
		// add an end-of-line character if this is '//'-style comment
		if c.Text[1] == '/' {
			result.WriteString("\n")
		}
	}

	// for '/*'-style comments, make sure to append EOL character to the comment
	// block
	if s := result.String(); !strings.HasSuffix(s, "\n") {
		result.WriteString("\n")
	}

	return result.String()
}

func main() {
	flag.Usage = func() {
		fmt.Fprint(os.Stderr, `
impl generates method stubs for recv to implement iface.

impl [-dir directory] <recv> <iface>

`[1:])
		flag.PrintDefaults()
		fmt.Fprint(os.Stderr, `

Examples:

impl 'f *File' io.Reader
impl Murmur hash.Hash
impl -dir $GOPATH/src/github.com/josharian/impl Murmur hash.Hash

Don't forget the single quotes around the receiver type
to prevent shell globbing.
`[1:])
		os.Exit(2)
	}
	flag.Parse()

	if len(flag.Args()) < 2 {
		flag.Usage()
	}

	recv, iface := flag.Arg(0), flag.Arg(1)
	if !validReceiver(recv) {
		fatal(fmt.Sprintf("invalid receiver: %q", recv))
	}

	if *flagSrcDir == "" {
		if dir, err := os.Getwd(); err == nil {
			*flagSrcDir = dir
		}
	}

	recvPkg := *flagRecvPkg
	if recvPkg == "" {
		//  "   s *Struct   " , receiver: Struct
		recvs := strings.Fields(recv)
		receiver := recvs[len(recvs)-1] // note that this correctly handles "s *Struct" and "*Struct"
		receiver = strings.TrimPrefix(receiver, "*")
		pkg, _, err := typeSpec("", Type{Name: receiver}, *flagSrcDir)
		if err == nil {
			recvPkg = pkg.Package.Name
		}
	}

	fns, err := funcs(iface, *flagSrcDir, recvPkg, EmitComments(*flagComments))
	if err != nil {
		fatal(err)
	}

	// Get list of already implemented funcs
	implemented, err := implementedFuncs(fns, recv, *flagSrcDir)
	if err != nil {
		fatal(err)
	}

	src := genStubs(recv, fns, implemented)
	fmt.Print(string(src))
}

func fatal(msg any) {
	fmt.Fprintln(os.Stderr, msg)
	os.Exit(1)
}
