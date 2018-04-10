
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using VC;
using Outcome = VC.VCGen.Outcome;
using Bpl = Microsoft.Boogie;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using Microsoft.Boogie.GraphUtil;

namespace Microsoft.Boogie.Houdini {


    
    class DLHoudiniErrorReporter : ProverInterface.ErrorHandler
    {
        public Model model;

        public DLHoudiniErrorReporter()
        {
            model = null;
        }

        public override void OnModel(IList<string> labels, Model model,  Outcome proverOutcome)
        {
            Debug.Assert(model != null);
            if(CommandLineOptions.Clo.PrintErrorModel >= 1) model.Write(Console.Out);
            this.model = model;
        }
    }

    public class DLHoudiniInternalError : System.ApplicationException
    {
        public DLHoudiniInternalError(string msg) : base(msg) { }
    };

    public static class ExtendsExpr
    {
        public static Expr replace(Expr expr, List<string> oldvars, List<Expr> newvars)
        {
            if (expr is LiteralExpr)
            {               
                LiteralExpr literalExpr = expr as LiteralExpr;
                return (literalExpr.Clone() as Expr);
            }
            else if (expr is IdentifierExpr)
            {
                IdentifierExpr identExpr = expr as IdentifierExpr;
                Debug.Assert(identExpr != null);
                int index = oldvars.IndexOf(identExpr.Name);
                Debug.Assert(index >= 0 && index < newvars.Count());
                Expr newExpr = newvars.ElementAt(index);                            
                return (newExpr.Clone() as Expr);
            }
            else if (expr is NAryExpr)
            {
                NAryExpr naryExpr = expr as NAryExpr;
                List<Expr> newargs = new List<Expr>();
                foreach (var exprarg in naryExpr.Args)
                {
                    newargs.Add(replace(exprarg, oldvars, newvars));                    
                }
                return new NAryExpr(Token.NoToken, naryExpr.Fun, newargs);
            }

            throw new DLHoudiniInternalError("Error: learned invariant is an expression of unexpected type!");
        }

        public static Expr conjunction(List<Expr> exprs)
        {
            if (exprs.Count() == 0)
            {
                return Expr.False;
            }
            else if (exprs.Count() == 1)
            {
                return exprs.ElementAt(0);
            }
            else
            {
                Expr lhs = exprs.ElementAt(0);
                exprs.RemoveAt(0);
                Expr rhs = conjunction(exprs);
                return Expr.And(lhs, rhs);
            }
        }

        /*
         * Assume that the argument has atleast one list of exprs in it.
         */
        public static Expr disjunction(List<List<Expr>> exprs)
        {
            Debug.Assert(exprs.Count() > 0);
            if (exprs.Count() == 1)
            {
                return conjunction(exprs.ElementAt(0));
            }
            else
            {
                Expr lhs = conjunction(exprs.ElementAt(0));
                exprs.RemoveAt(0);
                Expr rhs = disjunction(exprs);
                return Expr.Or(lhs, rhs);
            }            
        }

        public static bool EqualityComparer(Expr model, Expr newmodel)
        {
            /*
            if (model is LiteralExpr && newmodel is LiteralExpr)
            {
                LiteralExpr litmodel = model as LiteralExpr;
                LiteralExpr litnewmodel = newmodel as LiteralExpr;
                if (litnewmodel.Val.GetType() == typeof(bool) && litmodel.Val.GetType() == typeof(bool))
                {
                    return litnewmodel.Val == litmodel.Val;
                }
                else if (litnewmodel.Val.GetType() == typeof(BigNum) && litmodel.Val.GetType() == typeof(BigNum))
                {
                    return litnewmodel.Val.Equals(litmodel);
                }
                else if (litnewmodel.Val.GetType() == typeof(BigDec) && litmodel.Val.GetType() == typeof(BigDec))
                {
                    litnewmodel.Val.
                }


                return (literalExpr.Clone() as Expr);
            }
            else if (model is IdentifierExpr && newmodel is IdentifierExpr)
            {
                IdentifierExpr identExpr = expr as IdentifierExpr;
                Debug.Assert(identExpr != null);
                int index = oldvars.IndexOf(identExpr.Name);
                Debug.Assert(index >= 0 && index < newvars.Count());
                Expr newExpr = newvars.ElementAt(index);
                return (newExpr.Clone() as Expr);
            }
            else if (expr is NAryExpr)
            {
                NAryExpr naryExpr = expr as NAryExpr;
                List<Expr> newargs = new List<Expr>();
                foreach (var exprarg in naryExpr.Args)
                {
                    newargs.Add(replace(exprarg, oldvars, newvars));
                }
                return new NAryExpr(Token.NoToken, naryExpr.Fun, newargs);
            }*/
            return model.ToString() == newmodel.ToString();            
        }
    }

    public interface IDLDomain 
    {
        bool constructModel(string funcName, Dictionary<string, Dictionary<string, Expr>> attr2Expr, Dictionary<string, int> functionID);  // returns whether the abstract value has changed?
        Expr Gamma(List<Expr> vars);
    }

    public class MyDomain : IDLDomain
    {
        List<string> vars;
        Expr model;

        public MyDomain(List<Variable> functionFormalParams) {
            vars = new List<string>();
            foreach (var v in functionFormalParams) {
                vars.Add(v.Name);
            }
            model = Expr.True;
        }

        public Expr Gamma(List<Expr> newvars) {
            return ExtendsExpr.replace(model, vars, newvars);
        }

        public bool constructModel(string funcName, Dictionary<string, Dictionary<string, Expr>> attr2Expr, Dictionary<string, int> functionID)
        {
            Debug.Assert(attr2Expr.Keys.Contains(funcName));
            Debug.Assert(functionID.Keys.Contains(funcName));
            return true;
        }
    }

    class DLHoudiniCounterexampleCollector : VerifierCallback 
    {
        public string currImpl;
        public List<Counterexample> real_errors;
        public List<Counterexample> conjecture_errors;
        public List<Counterexample> implication_errors;

        DLHoudini container;

        public DLHoudiniCounterexampleCollector(DLHoudini container) {
            this.container = container;
            Reset(null);
        }

        public void Reset(string impl) {
            currImpl = impl;

            real_errors = new List<Counterexample>();
            conjecture_errors = new List<Counterexample>();
            implication_errors = new List<Counterexample>();
        }

        public override void OnCounterexample(Counterexample ce, string reason) {
            bool cexAdded;
            if (container.HandleCounterExample(currImpl, ce, out cexAdded)) {
                real_errors.Add(ce);
            }
            else {
                if (cexAdded) {
                    conjecture_errors.Add(ce);
                }
                else {
                    implication_errors.Add(ce);
                }
            }
        }
    }

    public class DLHoudini {
        Dictionary<string, Function> existentialFunctions;
        Program program;
        Dictionary<string, Implementation> name2Impl;
        Dictionary<string, VCExpr> impl2VC;
        Dictionary<string, List<Tuple<string, Function, NAryExpr>>> impl2FuncCalls;
        // constant -> the naryexpr that it replaced
        Dictionary<string, NAryExpr> constant2FuncCall;

        // function -> its abstract value
        Dictionary<string, IDLDomain> function2Value;

        // impl -> functions assumed/asserted
        Dictionary<string, HashSet<string>> impl2functionsAsserted, impl2functionsAssumed;

        // funtions -> impls where assumed/asserted
        Dictionary<string, HashSet<string>> function2implAssumed, function2implAsserted;

        // impl -> handler, collector
        Dictionary<string, Tuple<ProverInterface.ErrorHandler, DLHoudiniCounterexampleCollector>> impl2ErrorHandler;

        // Essentials: VCGen, Prover
        VCGen vcgen;
        ProverInterface prover;

        // Stats
        TimeSpan proverTime;
        int numProverQueries;

        TimeSpan c5LearnerTime;
        int c5LearnerQueries;
        TimeSpan totaltime;
        TimeSpan jsontime;

        int numPosExamples;
        int numNegCounterExamples;
        int numImplications;
        int totalTreeSize;
        int lastTreeSize;
        int total_truetrue_implications;
        int last_truetrue_implications;
        int total_falsetrue_implications;
        int last_falsetrue_implications;
        int total_falsefalse_implications;
        int last_falsefalse_implications;
        bool VCisValid;

        // Z3 context for implementing the SMT-based ICE learner.
        HashSet<Tuple<List<Tuple<string, List<Model.Element>>>, List<Tuple<string, List<Model.Element>>>>> counterExamples;
        HashSet<Tuple<List<Tuple<string, List<Model.Element>>>, List<Tuple<string, List<Model.Element>>>>> implicationCounterExamples;        

        public DLHoudini(Program program) 
        {
            this.program = program;
            this.impl2VC = new Dictionary<string, VCExpr>();
            this.impl2FuncCalls = new Dictionary<string, List<Tuple<string, Function, NAryExpr>>>();
            this.existentialFunctions = new Dictionary<string, Function>();
            this.name2Impl = new Dictionary<string, Implementation>();
            this.impl2functionsAsserted = new Dictionary<string, HashSet<string>>();
            this.impl2functionsAssumed = new Dictionary<string, HashSet<string>>();
            this.function2implAsserted = new Dictionary<string, HashSet<string>>();
            this.function2implAssumed = new Dictionary<string, HashSet<string>>();
            this.impl2ErrorHandler = new Dictionary<string, Tuple<ProverInterface.ErrorHandler, DLHoudiniCounterexampleCollector>>();
            this.constant2FuncCall = new Dictionary<string, NAryExpr>();

            // Find the existential functions
            foreach (var func in program.Functions
                .Where(f => QKeyValue.FindBoolAttribute(f.Attributes, "existential")))
                existentialFunctions.Add(func.Name, func);

            this.function2Value = new Dictionary<string, IDLDomain>();
            foreach (var func in existentialFunctions.Values)
            {
                function2Value[func.Name] = new MyDomain(func.InParams);
            }

            counterExamples = new HashSet<Tuple<List<Tuple<string, List<Model.Element>>>, List<Tuple<string, List<Model.Element>>>>>();
            implicationCounterExamples = new HashSet<Tuple<List<Tuple<string, List<Model.Element>>>, List<Tuple<string, List<Model.Element>>>>>();

            existentialFunctions.Keys.Iter(f => function2implAssumed.Add(f, new HashSet<string>()));
            existentialFunctions.Keys.Iter(f => function2implAsserted.Add(f, new HashSet<string>()));

            // type check
            existentialFunctions.Values.Iter(func =>
                {
                    if (func.OutParams.Count != 1 || !func.OutParams[0].TypedIdent.Type.IsBool)
                        throw new DLHoudiniInternalError(string.Format("Existential function {0} must return bool", func.Name));
                    if (func.Body != null)
                        throw new DLHoudiniInternalError(string.Format("Existential function {0} should not have a body", func.Name));
                    func.InParams.Iter(v =>
                    {
                        if (!v.TypedIdent.Type.IsInt && !v.TypedIdent.Type.IsBool)
                        {
                            throw new DLHoudiniInternalError("TypeError: Illegal tpe, expecting int or bool");
                        }
                    });
                });
           
            Inline();

            this.vcgen = new VCGen(program, CommandLineOptions.Clo.SimplifyLogFilePath, CommandLineOptions.Clo.SimplifyLogFileAppend, new List<Checker>());
            this.prover = ProverInterface.CreateProver(program, CommandLineOptions.Clo.SimplifyLogFilePath, CommandLineOptions.Clo.SimplifyLogFileAppend, CommandLineOptions.Clo.ProverKillTime);

            this.proverTime = TimeSpan.Zero;
            this.numProverQueries = 0;

            var impls = program.TopLevelDeclarations.OfType<Implementation>().Where(
                    impl => impl != null && CommandLineOptions.Clo.UserWantsToCheckRoutine(cce.NonNull(impl.Name)) && !impl.SkipVerification);

            impls.Iter(impl => name2Impl.Add(impl.Name, impl));

            // Let's do VC Gen (and also build dependencies)
            name2Impl.Values.Iter(GenVC);

        }

        private void GenVC(Implementation impl)
        {
            ModelViewInfo mvInfo;
            Dictionary<int, Absy> label2absy;
            var collector = new DLHoudiniCounterexampleCollector(this);
            collector.OnProgress("HdnVCGen", 0, 0, 0.0);

            if (CommandLineOptions.Clo.Trace)
            {
                Console.WriteLine("Generating VC of {0}", impl.Name);
            }

            vcgen.ConvertCFG2DAG(impl);
            var gotoCmdOrigins = vcgen.PassifyImpl(impl, out mvInfo);

            // Inline functions
            (new InlineFunctionCalls()).VisitBlockList(impl.Blocks);

            ExtractQuantifiedExprs(impl);
            StripOutermostForall(impl);

            //ExtractBoolExprs(impl);

            //CommandLineOptions.Clo.PrintInstrumented = true;
            //using (var tt = new TokenTextWriter(Console.Out))
            //    impl.Emit(tt, 0);

            // Intercept the FunctionCalls of the existential functions, and replace them with Boolean constants
            var existentialFunctionNames = new HashSet<string>(existentialFunctions.Keys);
            var fv = new ReplaceFunctionCalls(existentialFunctionNames);
            fv.VisitBlockList(impl.Blocks);

            //using (var tt = new TokenTextWriter(Console.Out))
            //    impl.Emit(tt, 0);


            impl2functionsAsserted.Add(impl.Name, fv.functionsAsserted);
            impl2functionsAssumed.Add(impl.Name, fv.functionsAssumed);

            fv.functionsAssumed.Iter(f => function2implAssumed[f].Add(impl.Name));
            fv.functionsAsserted.Iter(f => function2implAsserted[f].Add(impl.Name));

            impl2FuncCalls.Add(impl.Name, fv.functionsUsed);
            fv.functionsUsed.Iter(tup => constant2FuncCall.Add(tup.Item2.Name, tup.Item3));

            HashSet<string> constantsAssumed = new HashSet<string>();
            fv.functionsUsed.Where(tup => impl2functionsAssumed[impl.Name].Contains(tup.Item1)).Iter(tup => constantsAssumed.Add(tup.Item2.Name));


            var gen = prover.VCExprGen;
            VCExpr controlFlowVariableExpr = CommandLineOptions.Clo.UseLabels ? null : gen.Integer(Microsoft.Basetypes.BigNum.ZERO);

            //var vcexpr = vcgen.P_GenerateVC(impl, constantsAssumed, controlFlowVariableExpr, out label2absy, prover.Context);
            var vcexpr = vcgen.GenerateVC(impl, controlFlowVariableExpr, out label2absy, prover.Context);

            if (!CommandLineOptions.Clo.UseLabels)
            {
                VCExpr controlFlowFunctionAppl = gen.ControlFlowFunctionApplication(gen.Integer(Microsoft.Basetypes.BigNum.ZERO), gen.Integer(Microsoft.Basetypes.BigNum.ZERO));
                VCExpr eqExpr = gen.Eq(controlFlowFunctionAppl, gen.Integer(Microsoft.Basetypes.BigNum.FromInt(impl.Blocks[0].UniqueId)));
                vcexpr = gen.Implies(eqExpr, vcexpr);
            }

            ProverInterface.ErrorHandler handler = null;
            if (CommandLineOptions.Clo.vcVariety == CommandLineOptions.VCVariety.Local)
                handler = new VCGen.ErrorReporterLocal(gotoCmdOrigins, label2absy, impl.Blocks, vcgen.incarnationOriginMap, collector, mvInfo, prover.Context, program);
            else
                handler = new VCGen.ErrorReporter(gotoCmdOrigins, label2absy, impl.Blocks, vcgen.incarnationOriginMap, collector, mvInfo, prover.Context, program);

            impl2ErrorHandler.Add(impl.Name, Tuple.Create(handler, collector));


            //Console.WriteLine("VC of {0}: {1}", impl.Name, vcexpr);

            // Create a macro so that the VC can sit with the theorem prover
            Macro macro = new Macro(Token.NoToken, impl.Name + "Macro", new List<Variable>(), new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "", Bpl.Type.Bool), false));
            prover.DefineMacro(macro, vcexpr);

            //Console.WriteLine("Function " + impl.Name + ":\n" + vcexpr.ToString() );


            // Store VC
            impl2VC.Add(impl.Name, gen.Function(macro));

            // HACK: push the definitions of constants involved in function calls
            // It is possible that some constants only appear in function calls. Thus, when
            // they are replaced by Boolean constants, it is possible that (get-value) will 
            // fail if the expression involves such constants. All we need to do is make sure
            // these constants are declared, because otherwise, semantically we are doing
            // the right thing.
            foreach (var tup in fv.functionsUsed)
            {
                // Ignore ones with bound varibles
                if (tup.Item2.InParams.Count > 0) continue;
                var tt = prover.Context.BoogieExprTranslator.Translate(tup.Item3);
                tt = prover.VCExprGen.Or(VCExpressionGenerator.True, tt);
                prover.Assert(tt, true);
            }
        }

        public VCGenOutcome ComputeSummaries()
        {
            // Compute SCCs and determine a priority order for impls
            var Succ = new Dictionary<string, HashSet<string>>();
            var Pred = new Dictionary<string, HashSet<string>>();
            name2Impl.Keys.Iter(s => Succ[s] = new HashSet<string>());
            name2Impl.Keys.Iter(s => Pred[s] = new HashSet<string>());

            foreach(var impl in name2Impl.Keys) {
                Succ[impl] = new HashSet<string>();
                impl2functionsAsserted[impl].Iter(f => 
                    function2implAssumed[f].Iter(succ =>
                        {
                            Succ[impl].Add(succ);
                            Pred[succ].Add(impl);
                        }));
            }

            var sccs = new StronglyConnectedComponents<string>(name2Impl.Keys,
                new Adjacency<string>(n => Pred[n]),
                new Adjacency<string>(n => Succ[n]));
            sccs.Compute();
            
            // impl -> priority
            var impl2Priority = new Dictionary<string, int>();
            int p = 0;
            foreach (var scc in sccs)
            {
                foreach (var impl in scc)
                {
                    impl2Priority.Add(impl, p);
                    p++;
                }
            }

            VCGenOutcome overallOutcome = null;

            var start = DateTime.Now;

            overallOutcome = LearnInv(impl2Priority);

            var elapsed = DateTime.Now;
            this.totaltime = elapsed - start;

            Console.WriteLine("Prover time = {0}", proverTime.TotalSeconds.ToString("F2"));
            Console.WriteLine("Number of prover queries = " + numProverQueries);

            if (CommandLineOptions.Clo.PrintAssignment)
            {
                // Print the existential functions
                existentialFunctions.Values.Iter(PrintFunction);
            }
            
            return overallOutcome;
        }

        private VCGenOutcome LearnInv(Dictionary<string, int> impl2Priority)
        {
            var worklist = new SortedSet<Tuple<int, string>>();
            name2Impl.Keys.Iter(k => worklist.Add(Tuple.Create(impl2Priority[k], k)));
            
            while (worklist.Any())
            {
                var impl = worklist.First().Item2;
                worklist.Remove(worklist.First());

                #region vcgen

                var gen = prover.VCExprGen;
                var terms = new List<Expr>();
                foreach (var tup in impl2FuncCalls[impl])
                {
                    var controlVar = tup.Item2;
                    var exprVars = tup.Item3;
                    var varList = new List<Expr>();
                    exprVars.Args.OfType<Expr>().Iter(v => varList.Add(v));

                    var args = new List<Expr>();
                    controlVar.InParams.Iter(v => args.Add(Expr.Ident(v)));
                    Expr term = Expr.Eq(new NAryExpr(Token.NoToken, new FunctionCall(controlVar), args),
                                 function2Value[tup.Item1].Gamma(varList));

                    if (controlVar.InParams.Count != 0)
                    {
                        term = new ForallExpr(Token.NoToken, new List<Variable>(controlVar.InParams.ToArray()),
                            new Trigger(Token.NoToken, true, new List<Expr> { new NAryExpr(Token.NoToken, new FunctionCall(controlVar), args) }),
                            term);
                    }
                    terms.Add(term);

                    /*
                    foreach (var variable in varList)
                    {
                        terms.Add(Expr.Le(variable, Expr.Literal(10)));
                        terms.Add(Expr.Ge(variable, Expr.Literal(-10)));
                    }
                    */
                }

                //var env = BinaryTreeAnd(terms, 0, terms.Count - 1);
                //env.Typecheck(new TypecheckingContext((IErrorSink)null));
                //var envVC = prover.Context.BoogieExprTranslator.Translate(env);
                //var vc = gen.Implies(envVC, impl2VC[impl]);

                if (CommandLineOptions.Clo.Trace)
                {
                    Console.WriteLine("Verifying {0}: ", impl);
                    //Console.WriteLine("env: {0}", envVC);
                    var envFuncs = new HashSet<string>();
                    impl2FuncCalls[impl].Iter(tup => envFuncs.Add(tup.Item1));
                    envFuncs.Iter(f => PrintFunction(existentialFunctions[f]));
                }

                #endregion vcgen

                VCExpr finalVC;
                bool hasIntegerVariable = true;

                for (int i = 0; i <= 1; i++)
                {
                    var handler = impl2ErrorHandler[impl].Item1;
                    var collector = impl2ErrorHandler[impl].Item2;
                    collector.Reset(impl);
                    implicationCounterExamples.Clear();
                    VCisValid = true;   // set to false if control reaches HandleCounterExample
                    //realErrorEncountered = false;
                    //newSamplesAdded = false;
                    //this.posNegCexAdded = false;

                    var start = DateTime.Now;

                    //prover.Push();
                    //prover.Assert(gen.Not(finalVC), true);
                    //prover.FlushAxiomsToTheoremProver();
                    //prover.Check();
                    //ProverInterface.Outcome proverOutcome = prover.CheckOutcomeCore(handler);

                    var inc = (DateTime.Now - start);
                    proverTime += inc;
                    numProverQueries++;

                    if (CommandLineOptions.Clo.Trace)
                        Console.WriteLine("Prover Time taken = " + inc.TotalSeconds.ToString());

                    //if (proverOutcome == ProverInterface.Outcome.TimeOut || proverOutcome == ProverInterface.Outcome.OutOfMemory)
                    //{
                    //    Console.WriteLine("Z3 Prover for implementation {0} times out or runs out of memory !", impl);
                    //    return new VCGenOutcome(proverOutcome, new List<Counterexample>());
                    //}

                    if (!VCisValid)
                    {
                        /* There was a counterexample found and acted upon while proving the method. */
                        if (collector.real_errors.Count > 0)
                        {
                            return new VCGenOutcome(ProverInterface.Outcome.Invalid, collector.real_errors);
                        }

                        if (collector.conjecture_errors.Count == 0)
                        {
                            // No positive or negative counter-example added. Need to add implication counter-examples
                            Debug.Assert(collector.implication_errors.Count > 0);
                            foreach (var cex in implicationCounterExamples)
                            {
                                AddCounterExample(cex);
                            }
                        }

                        //Debug.Assert(newSamplesAdded);
                        
                        HashSet<string> funcsChanged;
                        /*
                        if (!learn(out funcsChanged))
                        {
                            // learner timed out, ran into some errors, or if there is no consistent conjecture
                            prover.Pop();
                            if(collector.conjecture_errors.Count > 0)
                                return new VCGenOutcome(ProverInterface.Outcome.Invalid, collector.conjecture_errors);
                            else
                                return new VCGenOutcome(ProverInterface.Outcome.Invalid, collector.implication_errors);
                        }
                       */

                        // propagate dependent guys back into the worklist, including self
                        var deps = new HashSet<string>();
                        deps.Add(impl);
                        funcsChanged.Iter(f => deps.UnionWith(function2implAssumed[f]));
                        funcsChanged.Iter(f => deps.UnionWith(function2implAsserted[f]));

                        deps.Iter(s => worklist.Add(Tuple.Create(impl2Priority[s], s)));
                         

                        // break out of the loop that iterates over various bounds.
                        prover.Pop();
                        break;
                    }
                    else
                    {
                        prover.Pop();
                    }
                }
            }
            // The program was verified
            return new VCGenOutcome(ProverInterface.Outcome.Valid, new List<Counterexample>());            
        }


        public bool HandleCounterExample(string impl, Counterexample error, out bool cexAdded)
        {
            // return true if a true error encountered.
            // return false if the error is due to a wrong choice of current conjecture.
            VCisValid = false;
            var cex = P_ExtractState(impl, error);

            // the counter-example does not involve any existential function ==> Is a real counter-example !
            if (cex.Item1.Count == 0 && cex.Item2.Count == 0)
            {
                //realErrorEncountered = true;
                cexAdded = false;
                return true;
            }

            if (cex.Item1.Count == 0 || cex.Item2.Count == 0)
            {
                cexAdded = true;
                AddCounterExample(cex);
                return false;
            }
            else
            {
                cexAdded = false;
                implicationCounterExamples.Add(cex);
                return false;
            }
        }


        public void AddCounterExample(Tuple<List<Tuple<string, List<Model.Element>>>, List<Tuple<string, List<Model.Element>>>> cex, 
                                      bool recordImplications = true)
        {
            List<Tuple<string, List<Model.Element>>> lhs = cex.Item1;
            List<Tuple<string, List<Model.Element>>> rhs = cex.Item2;

            //counterExamples.Add(cex);
            if (lhs.Count > 0 && rhs.Count > 0)
            {
                this.numImplications++;
                if(recordImplications && CommandLineOptions.Clo.Trace) 
                    Console.WriteLine("Implication added");
                else if (CommandLineOptions.Clo.Trace)
                    Console.WriteLine("Implication points added as unknowns (no edge added!)");                
            }
            else if (lhs.Count > 0)
            {
                this.numNegCounterExamples++;
                if (CommandLineOptions.Clo.Trace)
                    Console.WriteLine("Negative example added");
            }
            else
            {
                this.numPosExamples++;
                if (CommandLineOptions.Clo.Trace)
                    Console.WriteLine("Positive example added");
            }

            //RecordCexForC5(cex, recordImplications);
        }
        

        private Tuple<List<Tuple<string, List<Model.Element>>>, List<Tuple<string, List<Model.Element>>>> P_ExtractState(string impl, Counterexample error)
        {
            var lastBlock = error.Trace.Last() as Block;
            AssertCmd failingAssert = null;

            CallCounterexample callCounterexample = error as CallCounterexample;
            if (callCounterexample != null)
            {
                Procedure failingProcedure = callCounterexample.FailingCall.Proc;
                Requires failingRequires = callCounterexample.FailingRequires;
                failingAssert = lastBlock.Cmds.OfType<AssertRequiresCmd>().FirstOrDefault(ac => ac.Requires == failingRequires);
            }
            ReturnCounterexample returnCounterexample = error as ReturnCounterexample;
            if (returnCounterexample != null)
            {
                Ensures failingEnsures = returnCounterexample.FailingEnsures;
                failingAssert = lastBlock.Cmds.OfType<AssertEnsuresCmd>().FirstOrDefault(ac => ac.Ensures == failingEnsures);
            }
            AssertCounterexample assertCounterexample = error as AssertCounterexample;
            if (assertCounterexample != null)
            {
                failingAssert = lastBlock.Cmds.OfType<AssertCmd>().FirstOrDefault(ac => ac == assertCounterexample.FailingAssert);
            }
            Debug.Assert(failingAssert != null);

            // extract the lhs of the returned tuple from the AssumeCmds
            /*
            List<Tuple<string, List<Model.Element>>> lhs = new List<Tuple<string, List<Model.Element>>>();
            foreach (var cmd in error.AssumedCmds) 
            {
                AssumeCmd assumeCmd = cmd as AssumeCmd;
                Debug.Assert(assumeCmd != null);
                lhs.AddRange(P_ExtractState(impl, assumeCmd.Expr, error.Model));
            }
            */

            List<Tuple<string, List<Model.Element>>> rhs = new List<Tuple<string, List<Model.Element>>>();
            rhs = P_ExtractState(impl, failingAssert.Expr, error.Model);
            return Tuple.Create(lhs, rhs);
        }

        private List<Tuple<string, List<Model.Element>>> P_ExtractState(string impl, Expr expr, Model model)
        {            
            var funcsUsed = FunctionCollector.Collect(expr);

            var ret = new List<Tuple<string, List<Model.Element>>>();

            foreach (var tup in funcsUsed.Where(t => t.Item2 == null))
            {
                var constant = tup.Item1;
                if (!constant2FuncCall.ContainsKey(constant.Name))
                    continue;

                var func = constant2FuncCall[constant.Name];
                var funcName = (func.Fun as FunctionCall).FunctionName;
                var vals = new List<Model.Element>();
                prover.Context.BoogieExprTranslator.Translate(func.Args).Iter(ve => vals.Add(getValue(ve, model)));
                ret.Add(Tuple.Create(funcName, vals));
            }

            foreach (var tup in funcsUsed.Where(t => t.Item2 != null))
            {
                var constant = tup.Item1;
                var boundExpr = tup.Item2;

                if (!constant2FuncCall.ContainsKey(constant.Name))
                    continue;

                // There are some bound variables (because the existential function was inside an \exists).
                // We must find an assignment for bound varibles 

                // First, peice apart the existential functions
                var cd = new Duplicator();
                var tup2 = ExistentialExprModelMassage.Massage(cd.VisitExpr(boundExpr.Body));
                var be = tup2.Item1;
                Expr env = Expr.True;
                foreach (var ahFunc in tup2.Item2)
                {
                    var tup3 = impl2FuncCalls[impl].First(t => t.Item2.Name == ahFunc.Name);
                    var varList = new List<Expr>();
                    tup3.Item3.Args.OfType<Expr>().Iter(v => varList.Add(v));

                    env = Expr.And(env, function2Value[tup3.Item1].Gamma(varList));
                }
                be = Expr.And(be, Expr.Not(env));

                // map formals to constants
                var formalToConstant = new Dictionary<string, Constant>();
                foreach (var f in boundExpr.Dummies.OfType<Variable>())
                    formalToConstant.Add(f.Name, new Constant(Token.NoToken, new TypedIdent(Token.NoToken, f.Name + "@subst@" + (existentialConstCounter++), f.TypedIdent.Type), false));
                be = Substituter.Apply(new Substitution(v => formalToConstant.ContainsKey(v.Name) ? Expr.Ident(formalToConstant[v.Name]) : Expr.Ident(v)), be);
                formalToConstant.Values.Iter(v => prover.Context.DeclareConstant(v, false, null));

                var reporter = new AbstractHoudiniErrorReporter();
                var ve = prover.Context.BoogieExprTranslator.Translate(be);
                prover.Assert(ve, true);
                prover.Check();
                var proverOutcome = prover.CheckOutcomeCore(reporter);
                if (proverOutcome != ProverInterface.Outcome.Invalid)
                    continue;
                model = reporter.model;

                var func = constant2FuncCall[constant.Name];
                var funcName = (func.Fun as FunctionCall).FunctionName;
                var vals = new List<Model.Element>();
                foreach (var funcArg in func.Args.OfType<Expr>())
                {
                    var arg = Substituter.Apply(new Substitution(v => formalToConstant.ContainsKey(v.Name) ? Expr.Ident(formalToConstant[v.Name]) : Expr.Ident(v)), funcArg);
                    vals.Add(getValue(prover.Context.BoogieExprTranslator.Translate(arg), model));
                }
                ret.Add(Tuple.Create(funcName, vals));

            }
            
            return ret;
        }

        private static int existentialConstCounter = 0;

        private List<Tuple<string, List<Model.Element>>> ExtractState(string impl, Expr expr, Model model)
        {
            var funcsUsed = FunctionCollector.Collect(expr);

            var ret = new List<Tuple<string, List<Model.Element>>>();

            foreach (var tup in funcsUsed.Where(t => t.Item2 == null))
            {
                var constant = tup.Item1;
                if (!constant2FuncCall.ContainsKey(constant.Name))
                    continue;

                var func = constant2FuncCall[constant.Name];
                var funcName = (func.Fun as FunctionCall).FunctionName;
                var vals = new List<Model.Element>();
                prover.Context.BoogieExprTranslator.Translate(func.Args).Iter(ve => vals.Add(getValue(ve, model)));
                ret.Add(Tuple.Create(funcName, vals));
            }

            foreach (var tup in funcsUsed.Where(t => t.Item2 != null))
            {
                var constant = tup.Item1;
                var boundExpr = tup.Item2;

                if (!constant2FuncCall.ContainsKey(constant.Name))
                    continue;

                // There are some bound variables (because the existential function was inside an \exists).
                // We must find an assignment for bound varibles 

                // First, peice apart the existential functions
                var cd = new Duplicator();
                var tup2 = ExistentialExprModelMassage.Massage(cd.VisitExpr(boundExpr.Body));
                var be = tup2.Item1;
                Expr env = Expr.True;
                foreach (var ahFunc in tup2.Item2)
                {
                    var tup3 = impl2FuncCalls[impl].First(t => t.Item2.Name == ahFunc.Name);
                    var varList = new List<Expr>();
                    tup3.Item3.Args.OfType<Expr>().Iter(v => varList.Add(v));

                    env = Expr.And(env, function2Value[tup3.Item1].Gamma(varList));
                }
                be = Expr.And(be, Expr.Not(env));

                // map formals to constants
                var formalToConstant = new Dictionary<string, Constant>();
                foreach (var f in boundExpr.Dummies.OfType<Variable>())
                    formalToConstant.Add(f.Name, new Constant(Token.NoToken, new TypedIdent(Token.NoToken, f.Name + "@subst@" + (existentialConstCounter++), f.TypedIdent.Type), false));
                be = Substituter.Apply(new Substitution(v => formalToConstant.ContainsKey(v.Name) ? Expr.Ident(formalToConstant[v.Name]) : Expr.Ident(v)), be);
                formalToConstant.Values.Iter(v => prover.Context.DeclareConstant(v, false, null));

                var reporter = new MLHoudiniErrorReporter();
                var ve = prover.Context.BoogieExprTranslator.Translate(be);
                prover.Assert(ve, true);
                prover.Check();
                var proverOutcome = prover.CheckOutcomeCore(reporter);
                if (proverOutcome != ProverInterface.Outcome.Invalid)
                    continue;
                model = reporter.model;

                var func = constant2FuncCall[constant.Name];
                var funcName = (func.Fun as FunctionCall).FunctionName;
                var vals = new List<Model.Element>();
                foreach (var funcArg in func.Args.OfType<Expr>())
                {
                    var arg = Substituter.Apply(new Substitution(v => formalToConstant.ContainsKey(v.Name) ? Expr.Ident(formalToConstant[v.Name]) : Expr.Ident(v)), funcArg);
                    vals.Add(getValue(prover.Context.BoogieExprTranslator.Translate(arg), model));
                }
                ret.Add(Tuple.Create(funcName, vals));

            }

            return ret;
        }

        // convert "foo(... forall e ...) to:
        //    (p iff forall e) ==> foo(... p ...) 
        // where p is a fresh boolean variable and foo is an existential constant
        private void ExtractQuantifiedExprs(Implementation impl)
        {
            var funcs = new HashSet<string>(existentialFunctions.Keys);
            foreach (var blk in impl.Blocks)
            {
                foreach (var acmd in blk.Cmds.OfType<AssertCmd>())
                {
                    var ret = ExtractQuantifiers.Extract(acmd.Expr, funcs);
                    acmd.Expr = ret.Item1;
                    impl.LocVars.AddRange(ret.Item2);
                }
            }
        }
        
        // convert "assert e1 && forall x: e2" to
        //    assert e1 && e2[x <- x@bound]
        private void StripOutermostForall(Implementation impl)
        {
            var funcs = new HashSet<string>(existentialFunctions.Keys);
            foreach (var blk in impl.Blocks)
            {
                foreach (var acmd in blk.Cmds.OfType<AssertCmd>())
                {
                    var ret = StripQuantifiers.Run(acmd.Expr, funcs);
                    acmd.Expr = ret.Item1;
                    impl.LocVars.AddRange(ret.Item2);
                }
            }
        }

        private void Inline()
        {
            if (CommandLineOptions.Clo.InlineDepth < 0)
                return;

            var callGraph = BuildCallGraph();

            foreach (Implementation impl in callGraph.Nodes)
            {
                InlineRequiresVisitor inlineRequiresVisitor = new InlineRequiresVisitor();
                inlineRequiresVisitor.Visit(impl);
            }

            foreach (Implementation impl in callGraph.Nodes)
            {
                FreeRequiresVisitor freeRequiresVisitor = new FreeRequiresVisitor();
                freeRequiresVisitor.Visit(impl);
            }

            foreach (Implementation impl in callGraph.Nodes)
            {
                InlineEnsuresVisitor inlineEnsuresVisitor = new InlineEnsuresVisitor();
                inlineEnsuresVisitor.Visit(impl);
            }

            foreach (Implementation impl in callGraph.Nodes)
            {
                impl.OriginalBlocks = impl.Blocks;
                impl.OriginalLocVars = impl.LocVars;
            }
            foreach (Implementation impl in callGraph.Nodes)
            {
                CommandLineOptions.Inlining savedOption = CommandLineOptions.Clo.ProcedureInlining;
                CommandLineOptions.Clo.ProcedureInlining = CommandLineOptions.Inlining.Spec;
                Inliner.ProcessImplementationForHoudini(program, impl);
                CommandLineOptions.Clo.ProcedureInlining = savedOption;
            }
            foreach (Implementation impl in callGraph.Nodes)
            {
                impl.OriginalBlocks = null;
                impl.OriginalLocVars = null;
            }

            Graph<Implementation> oldCallGraph = callGraph;
            callGraph = new Graph<Implementation>();
            foreach (Implementation impl in oldCallGraph.Nodes)
            {
                callGraph.AddSource(impl);
            }
            foreach (Tuple<Implementation, Implementation> edge in oldCallGraph.Edges)
            {
                callGraph.AddEdge(edge.Item1, edge.Item2);
            }
            int count = CommandLineOptions.Clo.InlineDepth;
            while (count > 0)
            {
                foreach (Implementation impl in oldCallGraph.Nodes)
                {
                    List<Implementation> newNodes = new List<Implementation>();
                    foreach (Implementation succ in callGraph.Successors(impl))
                    {
                        newNodes.AddRange(oldCallGraph.Successors(succ));
                    }
                    foreach (Implementation newNode in newNodes)
                    {
                        callGraph.AddEdge(impl, newNode);
                    }
                }
                count--;
            }
        }

        private void PrintFunction(Function function)
        {
            var tt = new TokenTextWriter(Console.Out);
            var invars = new List<Expr>(function.InParams.OfType<Variable>().Select(v => Expr.Ident(v)));
            function.Body = function2Value[function.Name].Gamma(invars);
            function.Emit(tt, 0);
            tt.Close();
        }

        private Graph<Implementation> BuildCallGraph()
        {
            Graph<Implementation> callGraph = new Graph<Implementation>();
            Dictionary<Procedure, HashSet<Implementation>> procToImpls = new Dictionary<Procedure, HashSet<Implementation>>();
            foreach (Declaration decl in program.TopLevelDeclarations)
            {
                Procedure proc = decl as Procedure;
                if (proc == null) continue;
                procToImpls[proc] = new HashSet<Implementation>();
            }
            foreach (Declaration decl in program.TopLevelDeclarations)
            {
                Implementation impl = decl as Implementation;
                if (impl == null || impl.SkipVerification) continue;
                callGraph.AddSource(impl);
                procToImpls[impl.Proc].Add(impl);
            }
            foreach (Declaration decl in program.TopLevelDeclarations)
            {
                Implementation impl = decl as Implementation;
                if (impl == null || impl.SkipVerification) continue;
                foreach (Block b in impl.Blocks)
                {
                    foreach (Cmd c in b.Cmds)
                    {
                        CallCmd cc = c as CallCmd;
                        if (cc == null) continue;
                        foreach (Implementation callee in procToImpls[cc.Proc])
                        {
                            callGraph.AddEdge(impl, callee);
                        }
                    }
                }
            }
            return callGraph;
        }


        class FunctionCollector : StandardVisitor
        {
            public List<Tuple<Function, ExistsExpr>> functionsUsed;
            ExistsExpr existentialExpr;

            public FunctionCollector()
            {
                functionsUsed = new List<Tuple<Function, ExistsExpr>>();
                existentialExpr = null;
            }

            public static List<Tuple<Function, ExistsExpr>> Collect(Expr expr)
            {
                var fv = new FunctionCollector();
                fv.VisitExpr(expr);
                return fv.functionsUsed;
            }

            public override QuantifierExpr VisitQuantifierExpr(QuantifierExpr node)
            {
                var oldE = existentialExpr;

                if (node is ExistsExpr)
                    existentialExpr = (node as ExistsExpr);

                node = base.VisitQuantifierExpr(node);

                existentialExpr = oldE;
                return node;
            }

            public override Expr VisitNAryExpr(NAryExpr node)
            {
                if (node.Fun is FunctionCall)
                {
                    var collector = new VariableCollector();
                    collector.Visit(node);

                    if(existentialExpr != null && existentialExpr.Dummies.Intersect(collector.usedVars).Any())
                        functionsUsed.Add(Tuple.Create((node.Fun as FunctionCall).Func, existentialExpr));
                    else
                        functionsUsed.Add(Tuple.Create<Function, ExistsExpr>((node.Fun as FunctionCall).Func, null));
                }

                return base.VisitNAryExpr(node);
            }
        }

        class P_FunctionCollector : StandardVisitor
        {
            public List<Function> functionsUsed;
            
            public P_FunctionCollector()
            {
                functionsUsed = new List<Function>();
            }

            public static List<Function> Collect(Expr expr)
            {
                var fv = new P_FunctionCollector();
                fv.VisitExpr(expr);
                return fv.functionsUsed;
            }

            public override BinderExpr VisitBinderExpr(BinderExpr node)
            {
                Debug.Assert(false);
 	            return base.VisitBinderExpr(node);
            }
                 
            public override Expr VisitNAryExpr(NAryExpr node)
            {
                if (node.Fun is FunctionCall)
                {
                    var collector = new VariableCollector();
                    collector.Visit(node);

                    functionsUsed.Add((node.Fun as FunctionCall).Func);
                }

                return base.VisitNAryExpr(node);
            }
        }

        private Model.Element getValue(VCExpr arg, Model model)
        {

            if (arg is VCExprLiteral)
            {
                //return model.GetElement(arg.ToString());
                return model.MkElement(arg.ToString());
            }

            else if (arg is VCExprVar)
            {
                var el = model.TryGetFunc(prover.Context.Lookup(arg as VCExprVar));
                if (el != null)
                {
                    Debug.Assert(el.Arity == 0 && el.AppCount == 1);
                    return el.Apps.First().Result;
                }
                else
                {
                    // Variable not defined; assign arbitrary value
                    if (arg.Type.IsBool)
                        return model.MkElement("false");
                    else if (arg.Type.IsInt)
                        return model.MkIntElement(0);
                    else
                        return null;
                }
            }
            else if (arg is VCExprNAry && (arg as VCExprNAry).Op is VCExprBvOp)
            {
                // support for BV constants
                var bvc = (arg as VCExprNAry)[0] as VCExprLiteral;
                if (bvc != null)
                {
                    var ret = model.TryMkElement(bvc.ToString() + arg.Type.ToString());
                    if (ret != null && (ret is Model.BitVector)) return ret;
                }
            }
           
            var val = prover.Evaluate(arg);
            if (val is int || val is bool || val is Microsoft.Basetypes.BigNum)
            {
                return model.MkElement(val.ToString());
            }
            else
            {
                Debug.Assert(false);
            }
            return null;
        }

        // Remove functions AbsHoudiniConstant from the expressions and substitute them with "true"
        class ExistentialExprModelMassage : StandardVisitor
        {
            List<Function> ahFuncs;

            public ExistentialExprModelMassage()
            {
                ahFuncs = new List<Function>();
            }

            public static Tuple<Expr, List<Function>> Massage(Expr expr)
            {
                var ee = new ExistentialExprModelMassage();
                expr = ee.VisitExpr(expr);
                return Tuple.Create(expr, ee.ahFuncs);
            }

            public override Expr VisitNAryExpr(NAryExpr node)
            {
                if (node.Fun is FunctionCall && (node.Fun as FunctionCall).FunctionName.StartsWith("AbsHoudiniConstant"))
                {
                    ahFuncs.Add((node.Fun as FunctionCall).Func);
                    return Expr.True;
                }

                return base.VisitNAryExpr(node);
            }
        }

    }

}
