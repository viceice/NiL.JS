﻿using NiL.JS;
using NiL.JS.Core;
using System;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Threading;
using System.Linq.Expressions;
using NiL.JS.Core.Functions;
using NiL.JS.Core.Interop;
using NiL.JS.BaseLibrary;
using NiL.JS.Extensions;
using System.Collections.Generic;
using System.Threading.Tasks;
using System.Dynamic;
using Debug = System.Diagnostics.Debug;

namespace Sandbox
{
    public class TestCallable : ICallable
    {
        public FunctionKind Kind
        {
            get
            {
                return FunctionKind.Function;
            }
        }

        public JSValue Call(JSValue targetObject, Arguments arguments)
        {
            Console.WriteLine("Called");

            return JSValue.Undefined;
        }

        public JSValue Construct(Arguments arguments)
        {
            Console.WriteLine("Constructed");

            return JSValue.Undefined;
        }

        public JSValue Construct(JSValue targetObject, Arguments arguments)
        {
            Console.WriteLine("Constructed with target");

            return JSValue.Undefined;
        }
    }

    public sealed class ExpandoObjectWrapper : JSObject
    {
        public int MyProperty
        {
            get;
            set;
        }

        private readonly IDictionary<string, object> _expandoObject;

        public ExpandoObjectWrapper(ExpandoObject expandoObject)
        {
            _expandoObject = expandoObject;
            ValueType = JSValueType.Object;
            Value = this;
        }

        protected override JSValue GetProperty(JSValue key, bool forWrite, PropertyScope propertyScope)
        {
            if (propertyScope <= PropertyScope.Own && key.ValueType != JSValueType.Symbol)
            {
                var keyString = key.ToString();
                key = keyString;

                object value;
                if (_expandoObject.TryGetValue(keyString, out value))
                    return Marshal(value);
            }

            return base.GetProperty(key, forWrite, propertyScope);
        }

        protected override bool DeleteProperty(JSValue name)
        {
            return _expandoObject.Remove(name.ToString());
        }

        protected override void SetProperty(JSValue key, JSValue value, PropertyScope memberScope, bool throwOnError)
        {
            if (memberScope <= PropertyScope.Own && key.ValueType != JSValueType.Symbol)
            {
                var keyString = key.ToString();
                key = keyString;

                _expandoObject[keyString] = value.Value;
            }

            base.SetProperty(key, value, memberScope, throwOnError);
        }
    }

    public class Program
    {
        public sealed class ClassWithTwoMethods
        {
            public void Method1(int prm0, params int[] prms)
            {
                Console.WriteLine(nameof(Method1));
                Console.WriteLine(prm0);
                Console.WriteLine(prms == null ? "<NULL>" : string.Join(", ", prms));
            }

            public void Method2(int prm0, int[] prms)
            {
                Console.WriteLine(nameof(Method2));
                Console.WriteLine(prm0);
                Console.WriteLine(prms == null ? "<NULL>" : string.Join(", ", prms));
            }
        }

        public class Sample
        {
        }

        public class SampleObject : CustomType
        {
            public Sample Sample => (Sample)Value;

            public SampleObject(Sample sample)
            {
                Value = sample;
            }

            protected override JSValue GetProperty(JSValue key, bool forWrite, PropertyScope propertyScope)
            {
                if (key.Value is string propertyName)
                {
                    switch (propertyName)
                    {
                        case "registerId": return "value of registerId";
                        case "unitId": return "value of unitId";
                    }
                }

                return NotExistsInObject;
            }
        }

        private sealed class InteropJsonSerializer : JsonSerializer
        {
            public InteropJsonSerializer(Type targetType)
                : base(targetType)
            {
            }

            public static string GetTypeName<T>(T value)
            {
                return value.GetType()?.FullName ?? "null";
            }
        }

        private class TestStruct
        {
            public int Value0 { get; set; }
            public string Value1 { get; set; }
            public double Value2;
        }

        private enum Enum
        {
            Value0,
            Value1,
            Value2,
        }

        private static void testEx()
        {
            var context = new Context();

            var dictionary = new Dictionary<ulong, TestStruct>();
            context.DefineConstructor(typeof(TestStruct));
            context.DefineVariable("test").Assign(new DictionaryWrapper<ulong, TestStruct>(dictionary));

            context.Eval(@"
var v = new TestStruct();
test[123] = { Value1: 'hello' };
console.log(Object.getOwnPropertyNames(test))");

            return;

            context.DefineVariable("test").Assign(new Action<TestStruct>(x =>
            {
                Debugger.Break();
            }));

            context.Eval("test({Value0:1,Value1:'str',Value2:123.456})");

            return;

            var strValue = "1234.4567e+12";
            var doubleValue = double.Parse(strValue, System.Globalization.CultureInfo.InvariantCulture);
            var sw = Stopwatch.StartNew();
            for (var i = 0; i < 10_000_000; i++)
            {
                //double.Parse(strValue, System.Globalization.CultureInfo.InvariantCulture);
                //NumberUtils.TryParse(strValue, 0, out _);

                //doubleValue.ToString(System.Globalization.CultureInfo.InvariantCulture);
                NumberUtils.DoubleToString(doubleValue);
            }

            Console.WriteLine(sw.Elapsed);
        }

        public sealed class MyTestModuleResolver : CachedModuleResolverBase
        {
            public override bool TryGetModule(ModuleRequest moduleRequest, out Module result)
            {
                if (moduleRequest.CmdArgument == "http://somesite.com/modules/arithmetic.js")
                {
                    var module = new Module(moduleRequest.CmdArgument, @"export function add(num1, num2) {
    return num1 + num2;
}");

                    result = module;
                    return true;
                }

                result = null;
                return false;
            }
        }

        private sealed class ModuleResolver : CachedModuleResolverBase
        {
            public override bool TryGetModule(ModuleRequest request, out Module result)
            {
                var currentDir = Directory.GetCurrentDirectory();
                if (File.Exists(currentDir + request.AbsolutePath))
                {
                    result = new Module(request.AbsolutePath, File.ReadAllText(currentDir + request.AbsolutePath));
                    return true;
                }

                result = null;
                return false;
            }
        }

        static void Main(string[] args)
        {
            //Parser.DefineCustomCodeFragment(typeof(NiL.JS.Test.SyntaxExtensions.UsingStatement));
            Thread.CurrentThread.Priority = ThreadPriority.AboveNormal;

            Context.DefaultGlobalContext.DebuggerCallback += (sender, e) => Debugger.Break();
            Context.DefaultGlobalContext.DefineVariable("$").Assign(JSValue.Wrap(
                new
                {
                    sleep = new Action<int>(time => Thread.Sleep(time)),
                    threadId = new Func<int>(() => Thread.CurrentThread.ManagedThreadId),
                    delay = new Func<int, Task>((x) => Task.Delay(x))
                }));
#if !PORTABLE
            Context.DefaultGlobalContext.DefineVariable("$nil").Assign(JSValue.Wrap(
                new
                {
                    GetCtor = new Func<string, JSValue>(name => JSValue.GetConstructor(NamespaceProvider.GetType(name)))
                }));
#endif
            //Context.DefaultGlobalContext.DefineVariable("alert").Assign(new ExternalFunction((t, a) => { System.Windows.Forms.MessageBox.Show(a[0].ToString()); return JSValue.Undefined; }));
            Context.DefaultGlobalContext.DefineVariable("print").Assign(new ExternalFunction((t, a) =>
            {
                for (var i = 0; i < a.Length; i++)
                    Console.WriteLine(a[i]);
                return JSValue.Undefined;
            }));

#if PORTABLE
            Context.DefaultGlobalContext.DefineVariable("console").Assign(JSValue.Wrap(new
            {
                log = new Action<Arguments>(arguments =>
                {
                    for (var i = 0; i < arguments.Length; i++)
                    {
                        if (i > 0)
                            System.Console.Write(" ");
                        var r = arguments[i].ToString();
                        System.Console.Write(r);
                    }
                    System.Console.WriteLine();
                })
            }));
#endif

            int mode = 3
                    ;
            switch (mode)
            {
                case -6:
                    {
                        var debug = false;

                        var module = runFile(
                            "tsc.js",
                            1,
                            x =>
                            {
                            //x.Debugging = true;
                                x.DebuggerCallback += (Context sender, DebuggerCallbackEventArgs e) =>
                                {
                                    if (debug)
                                    {
                                        if (new ContextDebuggerProxy(sender).Variables.Any(x => x.Value.ToString() == "ss"))
                                        {
                                            var i = 0;
                                        }
                                    }
                                };

                                x.DefineVariable("window").Assign(x.ThisBind);
                            });

                        var transpileFunction = module.Context.Eval(@"
input => {
    const result = ts.transpileModule(input, {
        compilerOptions: {
            target: ts.ScriptTarget.ES2015,
            module: ts.ModuleKind.ES2015,
            lib: [ 'ES2015' ],
            downlevelIteration: true,
        }
    });
    return result.outputText;
};
");

                        var tsc = transpileFunction.As<Function>().MakeDelegate<Func<string, string>>();

                        var typescriptSource = @"
import { SampleStore } from 'utiliread';
export default class Test {
    static inject = [SampleStore];
    constructor(private ss: SampleStore) {
    }
}";
                        //debug = true;
                        var transpiled = tsc(typescriptSource);

                        Debug.Assert(@"import { SampleStore } from 'utiliread';
export default class Test {
    constructor(ss) {
        this.ss = ss;
    }
}
Test.inject = [SampleStore];
" == transpiled);
                        break;
                    }
                case -5:
                    {
                        staticAnalyzer("modules/ftest.js");
                        break;
                    }
                case -3:
                    {
                        ///runFile("brain-browser.js");
                        runFile(@"sunspider-0.9.1\access-fannkuch.js", 150);
                        break;
                    }
                case -1:
                    {
                        //var currentTimeZone = TimeZone.CurrentTimeZone;
                        //var offset = currentTimeZone.GetType().GetField("m_ticksOffset", System.Reflection.BindingFlags.Instance | System.Reflection.BindingFlags.NonPublic);
                        //offset.SetValue(currentTimeZone, new TimeSpan(-8, 0, 0).Ticks);
                        //runFiles("custom/");
                        sputnikTests(@"tests\sputnik\ch15\15.1\");
                        sputnikTests(@"tests\sputnik\ch15\15.2\");
                        sputnikTests(@"tests\sputnik\ch15\15.3\");
                        sputnikTests(@"tests\sputnik\ch15\15.4\");
                        sputnikTests(@"tests\sputnik\ch15\15.5\"); // with some errors due double.toString() (8)
                        sputnikTests(@"tests\sputnik\ch15\15.6\");
                        sputnikTests(@"tests\sputnik\ch15\15.7\");
                        sputnikTests(@"tests\sputnik\ch15\15.8\"); // with some errors due accuracy comparison
                        sputnikTests(@"tests\sputnik\ch15\15.9\");
                        sputnikTests(@"tests\sputnik\ch15\15.10\"); // with 17 asserts
                        sputnikTests(@"tests\sputnik\ch15\15.11\");
                        sputnikTests(@"tests\sputnik\ch15\15.12\");
                        break;
                    }
                case 0:
                    {
                        // В текущем процессе часовой пояс будет -8:00:00. 
                        // Создатели sputnik'a не удосужились в своих тестах учитывать временную зону 
                        // и от всех требуют пребывания в указаном часовом поясе.
                        var currentTimeZone = TimeZone.CurrentTimeZone;
                        var offset = currentTimeZone.GetType().GetField("m_ticksOffset", System.Reflection.BindingFlags.Instance | System.Reflection.BindingFlags.NonPublic);
                        offset.SetValue(currentTimeZone, new TimeSpan(-8, 0, 0).Ticks);
                        //runFiles("custom/");
                        sputnikTests();
                        break;
                    }
                case 1:
                    {
                        // runFiles("custom/");
                        webkitTests();
                        break;
                    }
                case 2:
                    {
                        //var currentTimeZone = TimeZone.CurrentTimeZone;
                        //var offset = currentTimeZone.GetType().GetField("m_ticksOffset", System.Reflection.BindingFlags.Instance | System.Reflection.BindingFlags.NonPublic);
                        //offset.SetValue(currentTimeZone, new TimeSpan(-8, 0, 0).Ticks);
                        runFile(@"modules/ftest.js");
                        break;
                    }
                case 3:
                    {
                        testEx();
                        break;
                    }
                case 4:
                    {
                        compileTest();
                        break;
                    }
                case 5:
                    {
                        runFile("uglifyjs.js");
                        runFile("coffee-script.js");
                        runFile("linq.js");
                        runFile("arraytests.js");
                        runFile("d3.min.js");
                        runFile("knockout-3.3.0.js");
                        runFile("aes.js");
                        runFile("handlebars-v2.0.0.js");
                        break;
                    }
                case 6:
                    {
                        runFile("pbkdf.js");
                        break;
                    }
                case 8:
                    {
                        runFile("acorn_interpreter.js");
                        break;
                    }
                case 9:
                    {
                        runFile("d3.min.js");
                        break;
                    }
                case 10:
                    {
                        runFile("knockout-3.3.0.js");
                        break;
                    }
                case 11:
                    {
                        runFile("sunspider-regexp-dna.js");
                        break;
                    }
                case 12:
                    {
                        runTestFile(@"tests\sputnik\ch15\15.1\15.1.3\15.1.3.2\S15.1.3.2_A2.5_T1.js");
                        break;
                    }
                case 151:
                    {
                        // Global
                        sputnikTests(@"tests\sputnik\ch15\15.1\");
                        break;
                    }
                case 152:
                    {
                        // Object
                        sputnikTests(@"tests\sputnik\ch15\15.2\");
                        break;
                    }
                case 153:
                    {
                        // Function
                        sputnikTests(@"tests\sputnik\ch15\15.3\");
                        break;
                    }
                case 154:
                    {
                        // Array
                        sputnikTests(@"tests\sputnik\ch15\15.4\");
                        break;
                    }
                case 155:
                    {
                        // String
                        sputnikTests(@"tests\sputnik\ch15\15.5\");
                        break;
                    }
                case 156:
                    {
                        // Boolean
                        sputnikTests(@"tests\sputnik\ch15\15.6\");
                        break;
                    }
                case 157:
                    {
                        // Number
                        sputnikTests(@"tests\sputnik\ch15\15.7\");
                        break;
                    }
                case 158:
                    {
                        // Math
                        sputnikTests(@"tests\sputnik\ch15\15.8\");
                        break;
                    }
                case 159:
                    {
                        //var currentTimeZone = TimeZone.CurrentTimeZone;
                        //var offset = currentTimeZone.GetType().GetField("m_ticksOffset", System.Reflection.BindingFlags.Instance | System.Reflection.BindingFlags.NonPublic);
                        //offset.SetValue(currentTimeZone, new TimeSpan(-8, 0, 0).Ticks);
                        // Date
                        sputnikTests(@"tests\sputnik\ch15\15.9\");
                        break;
                    }
                case 1510:
                    {
                        // RegExp
                        sputnikTests(@"tests\sputnik\ch15\15.10\");
                        break;
                    }
                case 1511:
                    {
                        // Error
                        sputnikTests(@"tests\sputnik\ch15\15.11\");
                        break;
                    }
                case 1512:
                    {
                        // JSON
                        sputnikTests(@"tests\sputnik\ch15\15.12\");
                        break;
                    }
                case 100:
                    {
                        Context.DefaultGlobalContext.DefineVariable("load").Assign(new ExternalFunction((_th, e) =>
                        {
                            using (var f = new FileStream("v8\\" + e["0"], FileMode.Open, FileAccess.Read))
                            {
                                using (var sr = new StreamReader(f))
                                    Context.CurrentContext.Eval(sr.ReadToEnd(), true);
                            }
                            return null;
                        }));

                        runFile(@"v8\run.js");
                        break;
                    }
                case 101:
                    {
                        sunspider();
                        break;
                    }
                case 102:
                    {
                        dromaeoTests();
                        break;
                    }
                case 103:
                    {
                        kraken();
                        break;
                    }
                case 104:
                    {
                        cryptojs();
                        break;
                    }
            }

            GC.Collect(0);
            GC.Collect(1);
            GC.Collect(2);
            GC.WaitForPendingFinalizers();
            Console.WriteLine("GC.GetTotalMemory: " + GC.GetTotalMemory(true));
            Console.WriteLine("GC.CollectionCount: " + GC.CollectionCount(0));
            Console.WriteLine("GC.CollectionCount: " + GC.CollectionCount(1));
            Console.WriteLine("GC.CollectionCount: " + GC.CollectionCount(2));
            Console.WriteLine("GC.MaxGeneration: " + GC.MaxGeneration);
            //if (System.Windows.Forms.Application.OpenForms.Count != 0)
            //{
            //    while (System.Windows.Forms.Application.OpenForms.Count != 0)
            //    {
            //        System.Threading.Thread.Sleep(1);
            //        System.Windows.Forms.Application.DoEvents();
            //    }
            //}
            //else if (Debugger.IsAttached)
            //    Console.ReadKey();
        }

        private static void dromaeoTests()
        {
            const string rootPath = "dromaeo\\";

            Action<string> _ = Console.WriteLine;
            var sw = new Stopwatch();

            var runner = File.ReadAllText(rootPath + "runner.js");

            var tests = Directory.EnumerateFiles(rootPath + "tests\\", "*.js", SearchOption.AllDirectories)
                .Select(x => new Module(x, File.ReadAllText(x)))
                .ToArray();

            tests.All(x => x.Context.Eval(runner) != null);

            long _total = 0;
            var round = 0;
            long min = long.MaxValue;
            for (; round < 1; round++)
            {
                TimeSpan total = new TimeSpan();

                for (var i = 0; i < tests.Length; i++)
                {
                    _("Process " + tests[i].FilePath);

                    sw.Restart();
                    tests[i].Run();
                    sw.Stop();

                    total += sw.Elapsed;
                    _(sw.Elapsed.ToString());
                    _("");
                }
                _("Total: " + total);
                _total += total.Ticks;
                min = System.Math.Min(total.Ticks, min);
                GC.GetTotalMemory(true);
            }
            _("Average: " + new TimeSpan(_total / round));
            _("Minimum: " + new TimeSpan(min));
        }

        private static void sputnikTests(string folderPath = "tests\\sputnik\\")
        {
            bool showAll = false;
            bool refresh = true;
            int lastUpdate = Environment.TickCount;
            Action<string> _ = Console.WriteLine;
            var sw = new Stopwatch();
            int passed = 0;
            int failed = 0;
            string code;
            bool negative = false;
            string staCode = "";
            Module s = null;

            _("Sputnik testing begun...");

            _("Load sta.js...");
            using (var staFile = new FileStream("sta.js", FileMode.Open, FileAccess.Read))
                staCode = new StreamReader(staFile).ReadToEnd();

            _("Directory: \"" + Directory.GetParent(folderPath) + "\"");
            _("Scaning directory...");
            var fls = Directory.EnumerateFiles(folderPath, "*.js", SearchOption.AllDirectories).ToArray();
            _("Found " + fls.Length + " js-files");

            bool skipedShowed = false;
            sw.Start();
            for (int i = 0; i < fls.Length; i++)
            {
                if (i != (i ^ i) && !skipedShowed)
                    _("Skiped: " + i);
                skipedShowed = true;
                bool pass = true;
                try
                {
                    if (showAll)
                        Console.Write("Processing file \"" + fls[i] + "\" ");
                    var f = new FileStream(fls[i], FileMode.Open, FileAccess.Read);
                    var sr = new StreamReader(f);
                    code = sr.ReadToEnd();
                    sr.Dispose();
                    f.Dispose();
                    negative = code.IndexOf("@negative") != -1;
                    Context econtext = null;
                    if (refresh || s == null)
                    {
                        Context.ResetGlobalContext();
                        s = new Module(staCode);// инициализация
                        s.Run();
                        econtext = s.Context;
                    }
                    else
                        econtext = new Context(s.Context);
                    try
                    {
                        econtext.Eval(code, true);
                    }
                    finally
                    {
                        pass ^= negative;
                    }
                }
                catch (JSException e)
                {
                    pass = negative;
                    if (!pass)
                        Console.WriteLine(e.Message);
                }
                catch (Exception e)
                {
                    Debugger.Break();
                    Console.WriteLine(e);
                    pass = false;
                }
                if (pass)
                {
                    if (showAll)
                        _("Passed");
                    passed++;
                }
                else
                {
                    if (!showAll)
                        _("File: \"" + fls[i] + "\"" + Environment.NewLine);
                    else
                        _("Failed");
                    failed++;
                }
                if (Environment.TickCount - lastUpdate > 250)
                {
                    Console.Title = "passed: " + passed + ". failed: " + failed;
                    lastUpdate = Environment.TickCount;
                }
                //if (failed == 1)
                //    break;
            }
            sw.Stop();
            _("passed: " + passed + ". (" + (passed * 100 / fls.Length) + "%)");
            _("failed: " + failed);
            _("time: " + sw.Elapsed);
            _("Sputnik test complite");
        }

        private static void webkitTests(string folderPath = "tests\\webkit\\")
        {
            bool showAll = false;
            bool refresh = true;
            int lastUpdate = Environment.TickCount;

            Action<string> _ = Console.WriteLine;
            var sw = new Stopwatch();
            int passed = 0;
            int failed = 0;
            string code;
            string preCode = "";
            string postCode = "";
            Module s = null;
            _("webkit testing begun...");
            _("Load standalone-pre.js...");
            using (var staFile = new FileStream(folderPath + "resources\\standalone-pre.js", FileMode.Open, FileAccess.Read))
                preCode = new StreamReader(staFile).ReadToEnd();
            _("Load standalone-post.js...");
            using (var staFile = new FileStream(folderPath + "resources\\standalone-post.js", FileMode.Open, FileAccess.Read))
                postCode = new StreamReader(staFile).ReadToEnd();
            _("Directory: \"" + Directory.GetParent(folderPath) + "\"");

            _("Scaning directory...");
            var fls = Directory.EnumerateFiles(folderPath, "*.js", SearchOption.AllDirectories).ToArray();
            _("Found " + (fls.Length - 2) + " js-files");
            bool skipedShowed = false;
            sw.Start();
            for (int i = 0; i < fls.Length; i++)
            {
                if (i != 0 && !skipedShowed)
                    _("Skiped: " + i);
                skipedShowed = true;
                try
                {
                    if (fls[i].EndsWith("standalone-pre.js")
                        || fls[i].EndsWith("standalone-post.js"))
                        continue;
                    if (showAll)
                        Console.Write("Processing file \"" + fls[i] + "\" ");
                    var f = new FileStream(fls[i], FileMode.Open, FileAccess.Read);
                    var sr = new StreamReader(f, true);
                    code = sr.ReadToEnd();
                    sr.Dispose();
                    f.Dispose();
                    Context econtext = null;
                    if (refresh || s == null)
                    {
                        Context.ResetGlobalContext();
                        s = new Module(preCode);
                        s.Run();
                        econtext = s.Context;
                        s.Context.DefineVariable("print").Assign(new ExternalFunction((t, e) =>
                        {
                            bool fail = code.Length == 0; // она всегда не равна нулю, 
                            // но таким образом мы можем прочитать код без гуляния по стеку
                            string text;
                            for (var ti = 0; e != null && ti < e.Length; ti++)
                            {
                                text = e[ti].ToString();
                                if (ti == 0 && text == "FAIL")
                                    fail = true;
                                if (ti > 0)
                                    System.Console.Write(' ');
                                System.Console.Write(text);
                            }
                            if (fail)
                            {
                                failed++;
                                Debugger.Break();
                            }
                            else
                                passed++;
                            System.Console.WriteLine();
                            return JSValue.Undefined;
                        }));
                    }
                    else
                        econtext = new Context(s.Context);
                    try
                    {
                        econtext.Eval(code, true);
                    }
                    finally
                    {
                    }
                }
                catch (Exception e)
                {
                    System.Diagnostics.Debugger.Break();
                    Console.WriteLine(e);
                }
                if (Environment.TickCount - lastUpdate > 100)
                {
                    Console.Title = "passed: " + passed + ". failed: " + failed;
                    lastUpdate = Environment.TickCount;
                }
            }
            sw.Stop();
            _("time: " + sw.Elapsed);
            _("webkit test complite");
        }

        private static void benchmark()
        {
            Module s = null;
            var sw = new Stopwatch();
            int @case = 0;
            switch (@case)
            {
                case 0:
                    {
                        s = new Module(
            @"
function fib(x)
{
    if (x < 2)
        return 1;
    return fib(x - 1) + fib(x - 2);
}// 420 // 485 // 525 // 600 // 650
for (var i = 0; i < 700; i++) fib(20);
");
                        break;
                    }
                case 1:
                    {
                        s = new Module(
            @"
for (var i = 0; i < 24000000; i++) Math.abs(i);
");
                        break;
                    }
                case 2:
                    {
                        s = new Module(
            @"
function abs(x)
{
    return x < 0 ? -x : x;
}
for (var i = 0; i < 10000000; i++) abs(i * (1 - 2 * (i & 1)));
");
                        break;
                    }
            }
            s.Run();
            GC.Collect(0);
            GC.Collect(1);
            GC.Collect(2);
            GC.GetTotalMemory(true);
            sw.Start();
            s.Run();
            sw.Stop();
            Console.WriteLine(sw.Elapsed);
        }

        private static void compileTest()
        {
            /*
             * Я, крче, хз, но оно медленнее, чем без компиляции.
             * Либо мой зверинец классов реально быстрее,
             * чем Linq.Expressions, либо я как-то неправильно курю этот Linq.
             * Пускай, пока, этот метод поживёт. Может, когда-нибудь,
             * мою голову посетит прозрение и я пойму, что тут не так.
             * К слову, я пытался сам составлять байткод. 
             * Разницы в скорости не заметил, поэтому делаю вывод, что дело не в самих линках,
             * а в обработчике байт-кода. Но он, вроде как, должен быть с JIT-ом, 
             * который обязан выдавать код на порядок быстрее, чем постоянные виртуальные вызовы
             * и блуждания по AST. Но нет, результат, всё равно, медленнее.
             */
            var sw = new Stopwatch();
            var s = new Module(
@"
function isum(a, b)
{    
    return a + b;
}
var isum2 = isum;
for (var i = 0; i < 10000000; )
{
    i++;
    isum(2,3);
}
");
            Expression<Func<object, object, int>> nativeTest = (a, b) => ((((((int)(a) | 0) + ((int)(b) | 0)) | 0) + ((((int)(a) | 0) + ((int)(b) | 0)) | 0) | 0) + (((((int)(a) | 0) + ((int)(b) | 0)) | 0) + ((((int)(a) | 0) + ((int)(b) | 0)) | 0) | 0)) | 0;
            var cme = nativeTest.Compile();
            sw.Start();
            int sum = 0;
            for (int i = 0; i < 10000000; i++)
                sum += cme(2, 3);
            sw.Stop();
            Console.WriteLine(sum);
            Console.WriteLine(sw.Elapsed);

            sw.Restart();
            //s.TryCompile();
            sw.Stop();
            Console.WriteLine(sw.Elapsed);

            sw.Restart();
            s.Run();
            sw.Stop();
            Console.WriteLine(sw.Elapsed);
        }

        private static void staticAnalyzer(string fileName)
        {
            var f = new FileStream(fileName, FileMode.Open, FileAccess.Read);
            var sr = new StreamReader(f);
            var sw = new System.Diagnostics.Stopwatch();
            sw.Start();
            var s = new Module(sr.ReadToEnd(), (level, coords, message) =>
            {
                switch (level)
                {
                    case MessageLevel.Warning:
                        Console.ForegroundColor = ConsoleColor.Yellow;
                        break;
                    case MessageLevel.Recomendation:
                        Console.ForegroundColor = ConsoleColor.Green;
                        break;
                    case MessageLevel.Error:
                        Console.ForegroundColor = ConsoleColor.Red;
                        break;
                    case MessageLevel.CriticalWarning:
                        Console.ForegroundColor = ConsoleColor.Magenta;
                        break;
                    default:
                        Console.ForegroundColor = ConsoleColor.Gray;
                        break;
                }
                Console.Write(level);
                Console.Write(coords);
                Console.WriteLine(": " + message);
            });
            Console.ForegroundColor = ConsoleColor.Gray;
            sr.Dispose();
            f.Dispose();
            sw.Stop();
        }

        private static void cryptojs()
        {
            var folderPath = "crypto-js\\3.1.2";

            Action<string> _ = Console.WriteLine;
            var context = new Context();
            Action<string> load = path =>
            {
                path = folderPath + "\\" + path;
                _("Processing \"" + path + "\"");

                using (var fs = new FileStream(path, FileMode.Open, FileAccess.Read))
                using (var sr = new StreamReader(fs))
                {
                    var sw = Stopwatch.StartNew();
                    context.Eval(sr.ReadToEnd(), true);
                    sw.Stop();
                    _("Complite. Time: " + sw.Elapsed);
                }
            };
            load("src/core.js");
            load("src/lib-typedarrays.js");
            load("src/x64-core.js");
            load("src/enc-utf16.js");
            load("src/enc-base64.js");
            load("src/md5.js");
            load("src/sha1.js");
            load("src/sha256.js");
            load("src/sha224.js");
            load("src/sha512.js");
            load("src/sha384.js");
            load("src/sha3.js");
            load("src/ripemd160.js");
            load("src/hmac.js");
            load("src/pbkdf2.js");
            load("src/evpkdf.js");
            load("src/cipher-core.js");
            load("src/mode-cfb.js");
            load("src/mode-ctr.js");
            load("src/mode-ofb.js");
            load("src/mode-ecb.js");
            load("src/pad-ansix923.js");
            load("src/pad-iso10126.js");
            load("src/pad-zeropadding.js");
            load("src/pad-iso97971.js");
            load("src/pad-nopadding.js");
            load("src/rc4.js");
            load("src/rabbit.js");
            load("src/rabbit-legacy.js");
            load("src/aes.js");
            load("src/tripledes.js");

            load("../../yui.js");

            load("test/md5-profile.js");
            load("test/sha1-profile.js");
            load("test/sha256-profile.js");
            load("test/sha512-profile.js");
            load("test/sha3-profile.js");
            load("test/hmac-profile.js");
            load("test/pbkdf2-profile.js");
            load("test/evpkdf-profile.js");
            load("test/rc4-profile.js");
            load("test/rabbit-profile.js");
            load("test/aes-profile.js");
            load("test/des-profile.js");
            load("test/tripledes-profile.js");

            load("test/lib-base-test.js");
            load("test/lib-wordarray-test.js");
            load("test/lib-typedarrays-test.js");
            load("test/x64-word-test.js");
            load("test/x64-wordarray-test.js");
            load("test/enc-hex-test.js");
            load("test/enc-latin1-test.js");
            load("test/enc-utf8-test.js");
            load("test/enc-utf16-test.js");
            load("test/enc-base64-test.js");
            load("test/md5-test.js");
            load("test/sha1-test.js");
            load("test/sha256-test.js");
            load("test/sha224-test.js");
            load("test/sha512-test.js");
            load("test/sha384-test.js");
            load("test/sha3-test.js");
            load("test/ripemd160-test.js");
            load("test/hmac-test.js");
            load("test/pbkdf2-test.js");
            load("test/evpkdf-test.js");
            load("test/mode-cbc-test.js");
            load("test/mode-cfb-test.js");
            load("test/mode-ctr-test.js");
            load("test/mode-ofb-test.js");
            load("test/mode-ecb-test.js");
            load("test/pad-pkcs7-test.js");
            load("test/pad-ansix923-test.js");
            load("test/pad-iso10126-test.js");
            load("test/pad-zeropadding-test.js");
            load("test/pad-iso97971-test.js");
            load("test/lib-cipherparams-test.js");
            load("test/format-openssl-test.js");
            load("test/lib-serializablecipher-test.js");
            load("test/kdf-openssl-test.js");
            load("test/lib-passwordbasedcipher-test.js");
            load("test/rc4-test.js");
            load("test/rabbit-test.js");
            load("test/rabbit-legacy-test.js");
            load("test/aes-test.js");
            load("test/des-test.js");
            load("test/tripledes-test.js");

            context.Eval(@"YUI().use('test', 'console', function (Y) {
                Y.use('*', function (Y) {
                    new Y.Console({
                        style: 'block',
                        width: '600px',
                        height: '600px',
                        entryTemplate:
                          '<div class=""{entry_class} {cat_class} {src_class}"">' +
                          '    <p class=""{entry_meta_class}"">' +
                          '        <span class=""{entry_cat_class}"">{category}</span>' +
                          '    </p>' +
                          '    <pre class=""{entry_content_class}"">{message}</pre>' +
                          '</div>',
                        newestOnTop: false,
                        consoleLimit: 500,
                        render: true
                    });

                    Y.Test.Runner.run();
                });
            });", true);
        }

        private static void runFiles(string folderPath)
        {
            Action<string> _ = Console.WriteLine;
            _("Scaning directory...");
            var fls = Directory.EnumerateFiles(folderPath, "*.js", SearchOption.AllDirectories).ToArray();
            _("Found " + (fls.Length - 2) + " js-files");
            for (var i = 0; i < fls.Length; i++)
                runFile(fls[i]);
        }

        private static Module runFile(string filename, int times = 1, Action<Context> init = null)
        {
            Console.WriteLine("Processing file: " + filename);
            var f = new FileStream(filename, FileMode.Open, FileAccess.Read);
            var sr = new StreamReader(f);

            var sw = new Stopwatch();
            sw.Start();
            var module = new Module(filename, sr.ReadToEnd());
            sr.Dispose();
            f.Dispose();
            sw.Stop();
            Console.WriteLine("Compile time: " + sw.Elapsed);
            Console.WriteLine("-------------------------------------");

            init?.Invoke(module.Context);
            module.ModuleResolversChain.Add(new ModuleResolver());

            sw.Restart();
            while (times-- > 0)
                module.Run();
            sw.Stop();
            Console.WriteLine("-------------------------------------");
            Console.WriteLine("Complete.");
            Console.WriteLine("Time: " + sw.Elapsed);

            return module;
        }

        private static void runTestFile(string filename)
        {
            string staCode = "";
            using (var staFile = new FileStream("sta.js", FileMode.Open, FileAccess.Read))
                staCode = new StreamReader(staFile).ReadToEnd();
            Console.WriteLine("Start processing file: " + filename);
            var f = new FileStream(filename, FileMode.Open, FileAccess.Read);
            var sr = new StreamReader(f);
            var sw = new System.Diagnostics.Stopwatch();
            sw.Start();
            var s = new Module(staCode);
            sw.Stop();
            Console.WriteLine("Sta compile time: " + sw.Elapsed);
            sw.Restart();
            s.Run();
            sw.Stop();
            Console.WriteLine("Sta init time: " + sw.Elapsed);
            Console.WriteLine("Start evaluation of the file");
            Console.WriteLine("-------------------------------------");
            sw.Restart();
            s.Context.Eval(sr.ReadToEnd(), true);
            sw.Stop();
            Console.WriteLine("-------------------------------------");
            Console.WriteLine("Complite within " + sw.Elapsed);
            sr.Dispose();
            f.Dispose();
        }

        private static void sunspider()
        {
            var rootPath = "sunspider-0.9.1";

            Action<string> _ = Console.WriteLine;
            var sw = new Stopwatch();
            _("Directory: \"" + Directory.GetParent(rootPath) + "\"");
            _("Scaning directory...");

            var tests = Directory.EnumerateFiles(rootPath, "*.js", SearchOption.AllDirectories)
                .Select(x => new Module(x, File.ReadAllText(x)))
                .ToArray();

            long _total = 0;
            var round = 0;
            long min = long.MaxValue;
            for (; round < 10; round++)
            {
                TimeSpan total = new TimeSpan();

                for (var i = 0; i < tests.Length; i++)
                {
                    _("Process " + tests[i].FilePath);

                    sw.Restart();
                    tests[i].Run();
                    sw.Stop();

                    total += sw.Elapsed;
                    _(sw.Elapsed.ToString());
                }
                _("Total: " + total);
                _total += total.Ticks;
                min = System.Math.Min(total.Ticks, min);
                GC.GetTotalMemory(true);
            }
            _("Average: " + new TimeSpan(_total / round));
            _("Minimum: " + new TimeSpan(min));
        }

        private static void kraken()
        {
            var folderPath = "kraken-1.1";

            Action<string> _ = Console.WriteLine;
            var sw = new Stopwatch();
            _("Directory: \"" + Directory.GetParent(folderPath) + "\"");
            _("Scaning directory...");
            var fls = Directory.EnumerateFiles(folderPath, "*.js", SearchOption.AllDirectories).ToArray();
            _("Found " + fls.Length + " js-files");

            long _total = 0;
            var round = 0;
            long min = long.MaxValue;
            Context.ResetGlobalContext();
            for (; round < 1; round++)
            {
                TimeSpan total = new TimeSpan();

                for (var i = 0; i < fls.Length;)
                {
                    string data, body;
                    using (var f = new FileStream(fls[i++], FileMode.Open, FileAccess.Read))
                    using (var sr = new StreamReader(f))
                        data = sr.ReadToEnd();
                    _("Process " + fls[i]);
                    using (var f = new FileStream(fls[i++], FileMode.Open, FileAccess.Read))
                    using (var sr = new StreamReader(f))
                        body = sr.ReadToEnd();

                    sw.Restart();
                    var script = new Module(data);
                    script.Context.DefineVariable("print").Assign(new ExternalFunction((t, a) =>
                    {
                        for (var j = 0; j < a.Length; j++)
                            System.Console.WriteLine(a[j]);
                        return JSValue.Undefined;
                    }));
                    script.Run();
                    script.Context.Eval(body, true);
                    sw.Stop();
                    total += sw.Elapsed;
                    _(sw.Elapsed.ToString());
                    Context.ResetGlobalContext();
                    GC.Collect(0);
                    GC.Collect(1);
                    GC.Collect(2);
                    GC.GetTotalMemory(true);
                }
                _("Total: " + total);
                _total += total.Ticks;
                min = System.Math.Min(total.Ticks, min);
            }
            _("Average: " + new TimeSpan(_total / round));
            _("Minimum: " + new TimeSpan(min));
        }
    }
}
