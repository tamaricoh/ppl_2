// L3-eval.ts
// Evaluator with Environments model

import { map } from "ramda";
import {
  isBoolExp,
  isCExp,
  isLitExp,
  isNumExp,
  isPrimOp,
  isStrExp,
  isVarRef,
  isAppExp,
  isDefineExp,
  isIfExp,
  isLetExp,
  isProcExp,
  Binding,
  VarDecl,
  CExp,
  Exp,
  IfExp,
  LetExp,
  ProcExp,
  Program,
  parseL3Exp,
  DefineExp,
  ClassExp,
  isClassExp,
  isBinding,
  makeClassExp,
} from "./L3-ast";
import { applyEnv, makeEmptyEnv, makeExtEnv, Env } from "./L3-env-env"; // isEmptyEnv
import {
  isClosure,
  makeClosureEnv,
  Closure,
  Value,
  isClass,
  makeClass,
  Class,
  isObject,
  makeObject,
  Object,
  isSymbolSExp,
  makeClassEnv,
  makeObjectEnv,
} from "./L3-value";
import { applyPrimitive } from "./evalPrimitive";
import { allT, first, rest, isEmpty, isNonEmptyList } from "../shared/list";
import { Result, makeOk, makeFailure, bind, mapResult } from "../shared/result";
import { parse as p } from "../shared/parser";
import { format } from "../shared/format";
import { env } from "process";

// ========================================================
// Eval functions

const applicativeEval = (exp: CExp, env: Env): Result<Value> =>
  isNumExp(exp)
    ? makeOk(exp.val)
    : isBoolExp(exp)
    ? makeOk(exp.val)
    : isStrExp(exp)
    ? makeOk(exp.val)
    : isPrimOp(exp)
    ? makeOk(exp)
    : isVarRef(exp)
    ? applyEnv(env, exp.var)
    : isLitExp(exp)
    ? makeOk(exp.val)
    : isIfExp(exp)
    ? evalIf(exp, env)
    : isProcExp(exp)
    ? evalProc(exp, env)
    : isLetExp(exp)
    ? evalLet(exp, env)
    : isAppExp(exp)
    ? bind(applicativeEval(exp.rator, env), (proc: Value) =>
        bind(
          mapResult((rand: CExp) => applicativeEval(rand, env), exp.rands),
          (args: Value[]) => applyProcedure(proc, args)
        )
      )
    : isClassExp(exp)
    ? evalClass(exp, env)
    : makeFailure('"let" not supported (yet)');

export const isTrueValue = (x: Value): boolean => !(x === false);

const evalIf = (exp: IfExp, env: Env): Result<Value> =>
  bind(applicativeEval(exp.test, env), (test: Value) =>
    isTrueValue(test)
      ? applicativeEval(exp.then, env)
      : applicativeEval(exp.alt, env)
  );

const evalProc = (exp: ProcExp, env: Env): Result<Closure> =>
  makeOk(makeClosureEnv(exp.args, exp.body, env));

// KEY: This procedure does NOT have an env parameter.
//      Instead we use the env of the closure.
const applyProcedure = (proc: Value, args: Value[]): Result<Value> =>
  isPrimOp(proc)
    ? applyPrimitive(proc, args)
    : isClosure(proc)
    ? applyClosure(proc, args)
    : isClass(proc)
    ? applyClass(proc, args, makeEmptyEnv()) //===========================
    : isObject(proc)
    ? applyObject(proc, args, makeEmptyEnv()) //===========================
    : makeFailure(`Bad procedure ${format(proc)}`);

const applyClosure = (proc: Closure, args: Value[]): Result<Value> => {
  const vars = map((v: VarDecl) => v.var, proc.params);
  return evalSequence(proc.body, makeExtEnv(vars, args, proc.env));
};

// Evaluate a sequence of expressions (in a program)
export const evalSequence = (seq: Exp[], env: Env): Result<Value> =>
  isNonEmptyList<Exp>(seq)
    ? evalCExps(first(seq), rest(seq), env)
    : makeFailure("Empty sequence");

const evalCExps = (first: Exp, rest: Exp[], env: Env): Result<Value> =>
  isDefineExp(first)
    ? evalDefineExps(first, rest, env)
    : isCExp(first) && isEmpty(rest)
    ? applicativeEval(first, env)
    : isCExp(first)
    ? bind(applicativeEval(first, env), (_) => evalSequence(rest, env))
    : first;

// Eval a sequence of expressions when the first exp is a Define.
// Compute the rhs of the define, extend the env with the new binding
// then compute the rest of the exps in the new env.
const evalDefineExps = (def: DefineExp, exps: Exp[], env: Env): Result<Value> =>
  bind(applicativeEval(def.val, env), (rhs: Value) =>
    evalSequence(exps, makeExtEnv([def.var.var], [rhs], env))
  );

// Main program
export const evalL3program = (program: Program): Result<Value> =>
  evalSequence(program.exps, makeEmptyEnv());

export const evalParse = (s: string): Result<Value> =>
  bind(p(s), (x) =>
    bind(parseL3Exp(x), (exp: Exp) => evalSequence([exp], makeEmptyEnv()))
  );

// LET: Direct evaluation rule without syntax expansion
// compute the values, extend the env, eval the body.
const evalLet = (exp: LetExp, env: Env): Result<Value> => {
  const vals = mapResult(
    (v: CExp) => applicativeEval(v, env),
    map((b: Binding) => b.val, exp.bindings)
  );
  const vars = map((b: Binding) => b.var.var, exp.bindings);
  return bind(vals, (vals: Value[]) =>
    evalSequence(exp.body, makeExtEnv(vars, vals, env))
  );
};

export const evalClass = (exp: ClassExp, env: Env): Result<Value> =>
  makeOk(makeClassEnv(exp.fields, exp.methods, env));

// const applyObject = (proc: Object, args: Value[], env: Env): Result<Value> => {
//   if (isSymbolSExp(args[0])) {
//     const arrayBinding = proc.class.methods;
//     if (arrayBinding.length === 0) {
//       return makeFailure("No methods found in proc.class.methods");
//     }
//     const str = args[0].val;
//     const search = arrayBinding.filter((v: Binding) => v.var.var === str);
//     if (search.length === 0) {
//       return makeFailure(`Unrecognized method: ${str}`);
//     }
//     const searchVal = search[0].val;
//     if (isProcExp(searchVal)) {
//       const searchArgs = searchVal.args;
//       const searchBody = searchVal.body;
//       // const objectEnv = proc.class.fields.reduce(
//       //   (accEnv, field, index) => makeEnv(field.var, proc.args[index], accEnv),

//       //   env
//       // );
//       const methodClosure = makeClosureEnv(searchArgs, searchBody, env);
//       return applyClosure(methodClosure, args.slice(1));
//     }
//     return makeFailure(`Found method is not a procedure`);
//   }
//   return makeFailure(`First argument is not a symbol`);
// };
const applyObject = (obj: Object, args: Value[], env: Env): Result<Value> => {
  if (isSymbolSExp(args[0])) {
    const methodName = args[0].val;
    const methodBinding = obj.class.methods.find(
      (b) => b.var.var === methodName
    );

    if (!methodBinding) {
      return makeFailure(`Unrecognized method: ${methodName}`);
    }

    if (isProcExp(methodBinding.val)) {
      const method = methodBinding.val;

      // Create an environment that includes the object's fields
      const objectEnv = obj.class.fields.reduce(
        (accEnv, field, index) =>
          makeExtEnv([field.var], [obj.args[index]], accEnv),
        env
      );

      const methodClosure = makeClosureEnv(method.args, method.body, objectEnv);
      return applyClosure(methodClosure, args.slice(1));
    } else {
      return makeFailure(`Method ${methodName} is not a procedure`);
    }
  } else {
    return makeFailure(
      `Expected a symbol for method name, but got ${format(args[0])}`
    );
  }
};

const applyClass = (proc: Class, args: Value[], env: Env): Result<Value> =>
  makeOk(makeObjectEnv(proc, args, env));
