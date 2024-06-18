import { map, zipWith } from "ramda";
import {
  isBoolExp,
  isLitExp,
  isNumExp,
  isPrimOp,
  isVarRef,
  isAppExp,
  isDefineExp,
  isIfExp,
  isLetExp,
  isProcExp,
  Binding,
  CExp,
  Exp,
  IfExp,
  ProcExp,
  Program,
  ClassExp,
  isClassExp,
  makeClassExp,
  makeVarDecl,
  makeProcExp,
  BoolExp,
  makeBoolExp,
  makeIfExp,
  makeAppExp,
  makePrimOp,
  makeLitExp,
  makeVarRef,
  isProgram,
  makeDefineExp,
  makeProgram,
  isExp,
  makeBinding,
} from "./L3-ast";
import { Result, makeOk, makeFailure, bind, mapResult } from "../shared/result";
import { makeSymbolSExp } from "./L3-value";
import { allT, first, rest, isEmpty, isNonEmptyList } from "../shared/list";
type NonEmptyList<T> = [T, ...T[]];
/*
Purpose: Transform ClassExp to ProcExp
Signature: class2proc(classExp)
Type: ClassExp => ProcExp
*/
export const class2proc = (exp: ClassExp): ProcExp =>
  makeProcExp(exp.fields, [
    makeProcExp([makeVarDecl("msg")], [buildIfExp(exp.methods)]),
  ]);

const buildIfExp = (bindings: Binding[]): IfExp | BoolExp =>
  isEmpty(bindings)
    ? makeBoolExp(false)
    : buildNonEmptyIfExp(bindings as NonEmptyList<Binding>);

const buildNonEmptyIfExp = (bindings: NonEmptyList<Binding>): IfExp | BoolExp =>
  bindings.length > 0
    ? makeIfExp(
        makeAppExp(makePrimOp("eq?"), [
          makeVarRef("msg"),
          makeLitExp(makeSymbolSExp(bindings[0].var.var)),
        ]),
        makeAppExp(bindings[0].val, []),
        bindings.length > 1
          ? buildNonEmptyIfExp(rest(bindings) as NonEmptyList<Binding>)
          : makeBoolExp(false)
      )
    : makeBoolExp(false);
/*
Purpose: Transform all class forms in the given AST to procs
Signature: lexTransform(AST)
Type: [Exp | Program] => Result<Exp | Program>
*/

export const lexTransform = (exp: Exp | Program): Result<Exp | Program> =>
  isProgram(exp)
    ? bind(mapResult(noClass_Exp, exp.exps), (exps: Exp[]) =>
        makeOk(makeProgram(exps))
      )
    : isExp(exp)
    ? noClass_Exp(exp)
    : makeFailure("Never");

export const noClass_Exp = (exp: Exp): Result<Exp> =>
  isDefineExp(exp)
    ? bind(noClass_CExp(exp.val), (val: CExp) =>
        makeOk(makeDefineExp(exp.var, val))
      )
    : noClass_CExp(exp);

export const noClass_CExp = (exp: CExp): Result<CExp> =>
  isNumExp(exp)
    ? makeOk(exp)
    : isBoolExp(exp)
    ? makeOk(exp)
    : isPrimOp(exp)
    ? makeOk(exp)
    : isVarRef(exp)
    ? makeOk(exp)
    : isAppExp(exp)
    ? makeOk(exp)
    : isIfExp(exp)
    ? makeOk(exp)
    : isProcExp(exp)
    ? makeOk(exp)
    : isLetExp(exp)
    ? makeOk(exp)
    : isClassExp(exp)
    ? bind(
        mapResult((binding: Binding) => noClass_CExp(binding.val), exp.methods),
        (vals: CExp[]) =>
          makeOk(
            class2proc(
              makeClassExp(
                exp.fields,
                zipWith(
                  makeBinding,
                  map((binding) => binding.var.var, exp.methods),
                  vals
                )
              )
            )
          )
      )
    : isLitExp(exp)
    ? makeOk(exp)
    : makeFailure(`Unexpected CExp: ${exp.tag}`);
