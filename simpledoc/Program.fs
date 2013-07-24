module simpledoc.Main

open System
open System.IO
open System.Xml
open System.Xml.XPath
open Microsoft.FSharp.Reflection
open Mono.Cecil
open Mono.Cecil.Cil
open System.Runtime.CompilerServices
open System.Runtime.Serialization

type Mono.Collections.Generic.Collection<'T> with member x.ToList with get() = x |> Seq.toList
let dirtyEscape (txt : string) = txt.Replace("<", "&lt;").Replace(">", "&gt;") 

let hasAttrib attrib (attrs : CustomAttribute list) =  attrs |> List.exists(fun x -> x.AttributeType.FullName = attrib)
let getAttrib attrib (attrs : CustomAttribute list) =  attrs |> List.tryFind(fun x -> x.AttributeType.FullName = attrib)

module PrettyPrint = 
    let ppmappingattribute (scf: SourceConstructFlags) = 
        match scf with 
        | SourceConstructFlags.Field -> "field"
        | SourceConstructFlags.Exception -> "exception"
        | SourceConstructFlags.Module -> "module"
        | SourceConstructFlags.UnionCase -> "union"
        | SourceConstructFlags.ObjectType -> "type"
        | SourceConstructFlags.RecordType -> "record"
        | SourceConstructFlags.Value -> "value"
        | SourceConstructFlags.SumType -> "discriminated union"
        | SourceConstructFlags.Closure -> "closure"
        | SourceConstructFlags.None -> "none"
        | _ -> failwithf "Unknown construct flag: %A" scf

    let rec pptypename (typ : TypeReference) =
        let genericargs =   
            if typ.IsGenericInstance then
                let gargs : string[] = 
                    (typ :?> GenericInstanceType).GenericArguments.ToList
                    |> List.map(pptypename)
                    |> Array.ofList
                
                if typ.Name = "FSharpFunc`2" then sprintf "(<fsharpfunc>%s</fsharpfunc>)" (String.Join(" -&gt; ", gargs))
                else sprintf "&lt;<genericargs>%s<genericargs>&gt;" (String.Join(", ", gargs))
            else ""
        
        let removeArityDecoration (typname : string) = 
            if typname.Contains("`") then typname.Substring(0, typname.IndexOf("`"))
            else typname
        
        let tick = if typ.IsGenericParameter then "<tick>'</tick>" else ""
        
        let typename =        
            [
                "System.Void", "unit"
                "System.Boolean", "bool"
                "System.String", "string"
                "System.Object", "obj"
                "System.Int32", "int"
                "System.Exception", "exn"
                "System.Byte", "byte"
                "System.IntPtr", "nativeint"
                "Microsoft.FSharp.Core.Unit", "unit"
                "Microsoft.FSharp.Collections.FSharpMap", "Map"
                "Microsoft.FSharp.Core.FSharpOption", "option"
                "Microsoft.FSharp.Collections.FSharpList", "List"
                "Microsoft.FSharp.Control.FSharpAsync", "Async"
                "Microsoft.FSharp.Core.FSharpFunc", ""
            ] 
            |> Map.ofList
            |> Map.tryFind (removeArityDecoration typ.FullName)
            |> defaultArg <| (removeArityDecoration typ.Name)
        
        sprintf "<pptypename>%s<type>%s</type>%s</pptypename>" tick typename genericargs

    let ppoperator (operator : MethodDefinition) =         
        if operator.IsSpecialName then
            let oper =
                if operator.Name.StartsWith("op_") then
                    operator.Name
                        .Substring(3)
                        .Replace("Greater", "&gt;")
                        .Replace("Less", "&lt;")
                        .Replace("Equals", "=")
                    |> sprintf "<op>%s</op>"
                elif operator.Name.StartsWith("get_") then
                    sprintf "<specialname class='get'>get</specialname> %s" (operator.Name.Substring(4))
                elif operator.Name.StartsWith("set_") then
                    sprintf "<specialname class='set'>set</specialname> %s" (operator.Name.Substring(4))
                elif operator.Name.StartsWith("add_") then
                    sprintf "<specialname class='add'>add</specialname> %s" (operator.Name.Substring(4))
                elif operator.Name.StartsWith("remove_") then
                    sprintf "<specialname class='remove'>remove</specialname> %s" (operator.Name.Substring(4))
                elif operator.Name.StartsWith("|") then
                    sprintf "<specialname class='activepattern'>active pattern</specialname> %s" operator.Name
                elif operator.Name = ".ctor" then
                    "<specialname class='new'>new</specialname>"
                else failwithf "Unknown specialname: %A %A" operator.Name operator        

            sprintf "<ppoperator>%s</ppoperator>" oper
        else operator.Name
            
    let ppparameters (param : ParameterReference) =
        let paramlist = 
            if param.Name = String.Empty then sprintf "<type>%s</type>" (pptypename param.ParameterType)
            else sprintf "(<name>%s</name> : <type>%s</type>)" param.Name (pptypename param.ParameterType)
            
        sprintf "<ppparameters>%s</ppparameters>" paramlist
        
    let ppmethod (func : MethodDefinition) = 
        let hasCompArgs = hasAttrib "Microsoft.FSharp.Core.CompilationArgumentCountsAttribute"
                
        let generics =   
            if not func.GenericParameters.ToList.IsEmpty then
                let gargs : string[] = 
                    func.GenericParameters.ToList 
                    |> List.map(pptypename)
                    |> Array.ofList
                sprintf "&lt;<genericargs>%s</genericargs>&gt;" (String.Join(", ", gargs))
            else ""

        if func.HasParameters then
            let pars =
                let pargs =
                    func.Parameters.ToArray()
                    |> Array.map(ppparameters)
                if hasCompArgs func.CustomAttributes.ToList || func.Parameters.Count = 1 then 
                    String.Join(" -&gt; ", pargs)                  
                else sprintf "(%s)" (String.Join(" * ", pargs))

            sprintf "<ppmethod><name>%s</name>%s = <params>%s</params> -&gt; <returntype>%s</returntype></ppmethod>" 
                (ppoperator func) generics pars (pptypename func.ReturnType)
        else
            sprintf "<ppmethod><name>%s</name>%s = <returntype>%s</returntype></ppmethod>" 
                (ppoperator func) generics (pptypename func.ReturnType)
    
    let pptype (typ: TypeDefinition) = 
        let maybeCMA = 
            typ.CustomAttributes.ToList |> List.tryFind(fun x -> x.AttributeType.Name = "CompilationMappingAttribute")
        let typeName = 
            match maybeCMA with 
            | Some cma -> 
                let head = cma.ConstructorArguments.ToList.Head 
                ppmappingattribute (head.Value :?> SourceConstructFlags)
            | None -> "type"
        
        sprintf "<pptype><type>%s</type> <name>%s</name></pptype>" typeName typ.FullName

    let ppcustomattribs (cattrs : CustomAttribute list) =
        sprintf "<debug class='customattribs'>%s</debug>" 
            (String.Join(",", (cattrs |> Array.ofList |> Array.map(fun x -> x.AttributeType.FullName))))
//sprintf "<debug_attrribs>%A</debug_attribs>" 
    let ppproperty (prop : PropertyDefinition) = 
        sprintf "<ppproperty><name>%s</name> : <type>%s</type></ppproperty>" 
            prop.Name (pptypename prop.PropertyType)

    let ppfield (field : FieldDefinition) = 
        //printfn "%A" field.FieldType
        sprintf "<ppfield><name>%s</name> : <type>%s</type></ppfield>" 
            field.Name field.FieldType.Name

let mutable currentContext = "";
let ioprintf format = Printf.kprintf (fun msg -> File.AppendAllText(currentContext, msg)) format

let xpath = new XPathDocument(Path.ChangeExtension(Environment.GetCommandLineArgs().[1], ".xml"))
let navi = xpath.CreateNavigator()
type docElements = 
| Method of MethodReference
| Type of TypeReference
| Property of PropertyReference

let docResolver (element: docElements) =
    let target = 
        let elpath =
            match element with 
            | Method x -> sprintf "starts-with(@name, 'M:%s')" (x.FullName.Split([|' '|]).[1].Split([|'('|]).[0])
            | Type x -> sprintf "@name='T:%s'" x.FullName
            | Property x -> sprintf "starts-with(@name, 'P:%s')" (x.FullName.Split([|' '|]).[1].Split([|'('|]).[0])
        elpath.Replace("/", ".").Replace("::", ".").Replace("()", "")
    
    //printf "<!-- docpath: %s (%A) -->" target element
    let newnavi = navi.SelectSingleNode(sprintf "//doc/members/member[%s]" target)
    if newnavi = null || newnavi.Value.Trim() = "" then ""
    else
        // dirty hack to make doc content look a little nicer
        let content = 
            newnavi.InnerXml
                .Replace("\r\n ", "\r\n")
                .Replace("<summary>\r\n", "<summary>")
                .Replace("\r\n</summary>", "</summary>")
        sprintf "<doc>%s</doc>" content

let nonUserFilter (attribs: CustomAttribute list) = 
    if attribs.Length = 0 then true
    else
        let hasAttrib name = (attribs |> List.exists (fun x -> x.AttributeType.Name = name))
                
        not (hasAttrib "DebuggerNonUserCodeAttribute"
        || hasAttrib "DebuggerBrowsableAttribute"
        || hasAttrib "DebuggerTypeProxyAttribute"
        //|| hasAttrib "DebuggerDisplayAttribute"
        || hasAttrib "CompilerGeneratedAttribute")

let rec handleMethod (meth: MethodDefinition) =
    let isPinvoke = (meth.Attributes &&& MethodAttributes.PInvokeImpl) = MethodAttributes.PInvokeImpl
    //let isStatic = (meth.Attributes &&& MethodAttributes.Static) = MethodAttributes.Static
    
    let strpinvoke = if isPinvoke then "<attribute>pinvoke</attribute>" else ""
    //let strstatic = if isStatic then "<attribute>static</attribute>" else ""
        
    ioprintf "<method>%s%s%s" strpinvoke
        (PrettyPrint.ppcustomattribs meth.CustomAttributes.ToList) (PrettyPrint.ppmethod meth)
    ioprintf "%s</method>" (docResolver (Method meth))
    
    meth.Overrides.ToList
    |> List.map (fun x -> x.Resolve())
    |> List.iter (handleMethod)

let handleProperty (prop: PropertyDefinition) = 
    ioprintf "<property>%s%s" 
        (PrettyPrint.ppcustomattribs prop.CustomAttributes.ToList) (PrettyPrint.ppproperty prop)
    ioprintf "%s</property>" (docResolver (Property prop))
    prop.OtherMethods.ToList
    |> List.iter (handleMethod)

let handleField (field: FieldDefinition) =
    ioprintf "<field>%s%s</field>" 
        (PrettyPrint.ppcustomattribs field.CustomAttributes.ToList) (PrettyPrint.ppfield field)

let handleEvent (event : EventDefinition) = 
    ioprintf "<event>%A</event>" event.Name

let rec handleType (typ : TypeDefinition) =
    let defType = 
        if typ.IsInterface then "interface"
        elif typ.IsEnum then "enum"
        else "definition" 
    
    if not typ.IsNested && not typ.IsInterface && not typ.IsEnum then
        if currentContext <> "" then
            ioprintf "<br />documentation generated for \"%s\" by <b>docuhax super mega alpha</b> ashleyis&lt;ashleyis@me.com&gt;" typ.Module.Assembly.FullName
            ioprintf "</body></html>"
        currentContext <- sprintf "%s.html" typ.Name
        ioprintf "<html><head><link rel='stylesheet' href='style.css' /></head><body><a href='index.html' class='homelink'>Home</a>"
    
    ioprintf "<%s>%s%s" 
        defType (PrettyPrint.ppcustomattribs typ.CustomAttributes.ToList) (PrettyPrint.pptype typ)
    ioprintf "%s" (docResolver (Type typ))
    
    let methods = 
        typ.Methods.ToList 
        |> List.filter (fun x -> nonUserFilter x.CustomAttributes.ToList)
        |> List.filter (fun x -> x.IsPublic)
    
    let staticMethods = methods |> List.filter (fun x -> x.IsStatic)
    let instanceMethods = methods |> List.filter (fun x -> not x.IsStatic)
    
    if not staticMethods.IsEmpty then
        ioprintf "<staticmethods>"
        staticMethods |> List.iter handleMethod
        ioprintf "</staticmethods>"

    if not instanceMethods.IsEmpty then
        ioprintf "<methods>"
        instanceMethods |> List.iter handleMethod
        ioprintf "</methods>"
    
    typ.NestedTypes.ToList
    |> List.filter (fun x -> nonUserFilter x.CustomAttributes.ToList)
    |> List.filter (fun x -> x.IsPublic || x.IsNestedPublic)
    |> List.iter handleType
    
    if typ.HasFields then
        ioprintf "<fields>"
        typ.Fields.ToList
        |> List.filter (fun x -> nonUserFilter x.CustomAttributes.ToList)
        |> List.filter (fun x -> not x.IsSpecialName) // MARK: i don't think this is the right way to hide __value etc
        |> List.iter handleField
        ioprintf "</fields>"
    
    if typ.HasProperties then
        ioprintf "<properties>"
        typ.Properties.ToList
        |> List.filter (fun x -> nonUserFilter x.CustomAttributes.ToList)
        |> List.iter handleProperty
        ioprintf "</properties>"
    
    if typ.HasInterfaces then
        let dispInterfaces = 
            typ.Interfaces.ToList
            |> List.map (fun x -> x.Resolve())
            |> List.filter (fun x -> nonUserFilter x.CustomAttributes.ToList)
        if not dispInterfaces.IsEmpty then
            ioprintf "<interfaces>"
            dispInterfaces |> List.iter (handleType)
            ioprintf "</interfaces>"
    
    typ.Events.ToList 
    |> List.filter (fun x -> nonUserFilter x.CustomAttributes.ToList)
    |> List.iter (handleEvent)
    
    ioprintf "</%s>" defType

let handleAssembly (asm : AssemblyDefinition) =
    asm.MainModule.Types.ToList 
    |> List.filter (fun x -> nonUserFilter x.CustomAttributes.ToList)
    |> List.filter (fun x -> x.IsPublic)
    |> List.iter handleType
    
    File.AppendAllText("index.html", "<html><head><link rel='stylesheet' href='style.css' /></head><body><h2>Table of contents</h2><toc>")
    asm.MainModule.Types.ToList 
    |> List.filter (fun x -> nonUserFilter x.CustomAttributes.ToList)
    |> List.filter (fun x -> x.IsPublic)
    |> List.iter (fun x -> 
        if (File.Exists(sprintf "%s.html" x.Name)) then
            File.AppendAllText("index.html", (sprintf "<a href='%s.html'>%s</a><br />" x.Name x.FullName)))
    File.AppendAllText("index.html", 
            sprintf "</toc><br />documentation generated for \"%s\" by <b>docuhax super mega alpha</b> ashleyis&lt;ashleyis@me.com&gt;</body></html>" asm.FullName)
    

[<EntryPoint>]
let main args =
    let target = args.[0]
    let readerParams = ReaderParameters(ReadingMode.Immediate)
    let asm = AssemblyDefinition.ReadAssembly(target, readerParams)
    handleAssembly asm
    0
