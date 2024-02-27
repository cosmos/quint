/* ----------------------------------------------------------------------------------
 * Copyright 2022 Informal Systems
 * Licensed under the Apache License, Version 2.0.
 * See LICENSE in the project root for license information.
 * --------------------------------------------------------------------------------- */

/**
 * Constraint generation for Quint's type system
 *
 * @author Gabriela Moreira
 *
 * @module
 */

import { IRVisitor } from '../ir/IRVisitor'
import {
  QuintApp,
  QuintAssume,
  QuintBool,
  QuintConst,
  QuintDef,
  QuintEx,
  QuintInstance,
  QuintInt,
  QuintLambda,
  QuintLet,
  QuintName,
  QuintOpDef,
  QuintStr,
  QuintVar,
  isAnnotatedDef,
  QuintTypeAlias,
} from '../ir/quintIr'
import { QuintAppType, QuintType, QuintVarType, Row, rowNames, typeNames } from '../ir/quintTypes'
import { expressionToString, rowToString, typeToString } from '../ir/IRprinting'
import { Either, left, mergeInMany, right } from '@sweet-monads/either'
import { Error, ErrorTree, buildErrorLeaf, buildErrorTree, errorTreeToString } from '../errorTree'
import { getSignatures } from './builtinSignatures'
import { Constraint, Signature, TypeScheme, toScheme } from './base'
import { Substitutions, applySubstitution, compose } from './substitutions'
import { LookupTable } from '../names/base'
import {
  fieldConstraints,
  fieldNamesConstraints,
  itemConstraints,
  matchConstraints,
  recordConstructorConstraints,
  tupleConstructorConstraints,
  variantConstraints,
  withConstraints,
} from './specialConstraints'
import { FreshVarGenerator } from '../FreshVarGenerator'
import { IRTransformer, transformType } from '../ir/IRTransformer'
import { fail } from 'assert'
import { zip } from '../util'

export type SolvingFunctionType = (
  _table: LookupTable,
  _constraint: Constraint
) => Either<Map<bigint, ErrorTree>, Substitutions>

// `validateArity(opName, args, pred, msg)` is `right(null)` if
// if `pred(args.length) === true`, and otherwise `left(err)`, where `err`
// is constructed using the given `opName` and `msg`.
//
// `msg` should contain a textual description of the expected argument
// length, e.g., ("1", "2", "even number of", ...).
//
// Use this for operators that cannot be typed in the Quint type system.
function validateArity(
  opcode: string,
  args: [QuintEx, QuintType][],
  pred: (arity: number) => Boolean,
  msg: String
): Either<Error, null> {
  if (!pred(args.length)) {
    return left(
      buildErrorLeaf(
        `Checking arity for application of ${opcode}`,
        `Operator expects ${msg} arguments but was given ${args.length}`
      )
    )
  } else {
    return right(null)
  }
}

// A visitor that collects types and constraints for a module's expressions
export class ConstraintGeneratorVisitor implements IRVisitor {
  // Inject dependency to allow manipulation in unit tests
  constructor(solvingFunction: SolvingFunctionType, table: LookupTable, types?: Map<bigint, TypeScheme>) {
    this.solvingFunction = solvingFunction
    this.table = table
    this.freshVarGenerator = new FreshVarGenerator()
    if (types) {
      this.types = types
    }
  }

  protected types: Map<bigint, TypeScheme> = new Map<bigint, TypeScheme>()
  protected errors: Map<bigint, ErrorTree> = new Map<bigint, ErrorTree>()

  private solvingFunction: SolvingFunctionType
  private constraints: Constraint[] = []

  private builtinSignatures: Map<string, Signature> = getSignatures()
  private table: LookupTable
  private freshVarGenerator: FreshVarGenerator

  // Track location descriptions for error tree traces
  private location: string = ''

  // A stack of free type variables and row variables for lambda expressions.
  // Nested lambdas add new entries to the stack, and pop them when exiting.
  private freeNames: { typeVariables: Set<string>; rowVariables: Set<string> }[] = []

  // int[a]
  //
  // TODO: Free type variables must also use the variables in the constructor
  //
  // type T[a] = Set[a]
  // type U[a, b] = (Set[a], List[b])
  //
  // U[int, int]
  // val x  = (Set(1,2), List(1,2))
  // val f : a => U[a, U[a, b]] = ...
  //
  // U[a, b] =.= U[int, int] /\ a =.= b /\ typeOf(x) =.= (Set[a], List[b])
  //
  // type MapT[a,b] = (Set[a], a => b) => Set[b]
  //
  // def map(s: Set[a], f: a => b): Set[b] = ...
  //
  getResult(): [Map<bigint, ErrorTree>, Map<bigint, TypeScheme>] {
    return [this.errors, this.types]
  }

  enterExpr(e: QuintEx) {
    this.location = `Generating constraints for ${expressionToString(e)}`
  }

  exitDef(def: QuintDef) {
    if (this.constraints.length > 0) {
      this.solveConstraints().map(subs => {
        if (isAnnotatedDef(def)) {
          checkAnnotationGenerality(subs, def.typeAnnotation).mapLeft(err =>
            this.errors.set(def.typeAnnotation?.id ?? def.id, err)
          )
        }
      })
    }
  }

  exitVar(e: QuintVar) {
    this.addToResults(e.id, right(toScheme(e.typeAnnotation)))
  }

  exitConst(e: QuintConst) {
    this.addToResults(e.id, right(toScheme(e.typeAnnotation)))
  }

  exitInstance(def: QuintInstance) {
    if (this.errors.size !== 0) {
      return
    }

    // For each override, ensure that the the type for the name and the type of
    // the value are the same
    def.overrides.forEach(([name, ex]) => {
      this.addToResults(name.id, this.typeForName(name.name, name.id, 2).map(toScheme))

      this.fetchResult(name.id).chain(originalType => {
        return this.fetchResult(ex.id).map(expressionType => {
          this.constraints.push({ kind: 'eq', types: [originalType.type, expressionType.type], sourceId: ex.id })
        })
      })
    })

    // Solve constraints here since this won't go through `exitDef`
    if (this.constraints.length > 0) {
      this.solveConstraints()
    }
  }

  //     n: t ∈ Γ
  // ----------------- (NAME)
  //  Γ ⊢ n: (t, true)
  exitName(e: QuintName) {
    if (this.errors.size !== 0) {
      return
    }
    this.addToResults(e.id, this.typeForName(e.name, e.id, 2).map(toScheme))
  }

  // Literals have always the same type and the empty constraint
  exitLiteral(e: QuintBool | QuintInt | QuintStr) {
    this.addToResults(e.id, right(toScheme({ kind: e.kind })))
  }

  //   op: q ∈ Γ   Γ ⊢  p0, ..., pn: (t0, c0), ..., (tn, cn)   a is fresh
  // ------------------------------------------------------------------------ (APP)
  //    Γ ⊢ op(p0, ..., pn): (a, q ~ (t0, ..., tn) => a ∧ c0 ∧ ... ∧ cn)
  exitApp(e: QuintApp) {
    if (this.errors.size !== 0) {
      return
    }

    const argsResult: Either<Error, [QuintEx, QuintType][]> = mergeInMany(
      e.args.map(e => {
        return this.fetchResult(e.id).map(r => [e, r.type])
      })
    )

    // We want `definedSignature` computed before the fresh variable `a` so that the
    // numbering of their fresh variables stays in order, with `a`, used for return types,
    // bearing the highest number.
    const definedSignature = this.typeForName(e.opcode, e.id, e.args.length)
    const a: QuintType = { kind: 'var', name: this.freshVarGenerator.freshVar('_t') }
    const result = argsResult
      .chain(results => {
        switch (e.opcode) {
          // Record operators
          case 'Rec':
            return validateArity(e.opcode, results, l => l % 2 === 0, 'even number of').chain(() =>
              recordConstructorConstraints(e.id, results, a)
            )
          case 'field':
            return validateArity(e.opcode, results, l => l === 2, '2').chain(() => fieldConstraints(e.id, results, a))
          case 'fieldNames':
            return validateArity(e.opcode, results, l => l === 1, '1').chain(() =>
              fieldNamesConstraints(e.id, results, a)
            )
          case 'with':
            return validateArity(e.opcode, results, l => l === 3, '3').chain(() => withConstraints(e.id, results, a))
          // Tuple operators
          case 'Tup':
            return validateArity(e.opcode, results, l => l > 0, 'at least one').chain(() =>
              tupleConstructorConstraints(e.id, results, a)
            )
          case 'item':
            return validateArity(e.opcode, results, l => l === 2, '2').chain(() => itemConstraints(e.id, results, a))
          // Sum type operators
          case 'variant':
            return validateArity(e.opcode, results, l => l === 2, '2').chain(() => variantConstraints(e.id, results, a))
          case 'matchVariant':
            return validateArity(e.opcode, results, l => l % 2 !== 0, 'odd number of').chain(() =>
              matchConstraints(e.id, results, a)
            )
          // Otherwise it's a standard operator with a definition in the context
          default:
            return definedSignature.map(t1 => {
              const t2: QuintType = { kind: 'oper', args: results.map(r => r[1]), res: a }
              const c: Constraint = { kind: 'eq', types: [t1, t2], sourceId: e.id }
              return [c]
            })
        }
      })
      .map(cs => {
        this.constraints.push(...cs)
        return toScheme(a)
      })

    this.addToResults(e.id, result)
  }

  enterLambda(expr: QuintLambda) {
    const lastParamNames = this.currentFreeNames()
    const paramNames = {
      typeVariables: new Set(lastParamNames.typeVariables),
      rowVariables: new Set(lastParamNames.rowVariables),
    }
    expr.params.forEach(p => {
      const varName = p.name === '_' ? this.freshVarGenerator.freshVar('_t') : `t_${p.name}_${p.id}`
      paramNames.typeVariables.add(varName)
      const paramTypeVar: QuintVarType = { kind: 'var', name: varName }
      this.addToResults(p.id, right(toScheme(paramTypeVar)))
      if (p.typeAnnotation) {
        this.addTypeEqConstraint(paramTypeVar, p.typeAnnotation, p.id)
      }
    })

    this.freeNames.push(paramNames)
  }

  //    Γ ∪ {p0: t0, ..., pn: tn} ⊢ e: (te, c)    t0, ..., tn are fresh
  // ---------------------------------------------------------------------- (LAMBDA)
  //            Γ ⊢ (p0, ..., pn) => e: ((t0, ..., tn) => te, c)
  exitLambda(e: QuintLambda) {
    if (this.errors.size !== 0) {
      return
    }
    const result = this.fetchResult(e.expr.id).chain(resultType => {
      const paramTypes = mergeInMany(e.params.map(p => this.fetchResult(p.id).map(e => this.newInstance(e))))
      return paramTypes
        .map((ts): TypeScheme => {
          const newType: QuintType = { kind: 'oper', args: ts, res: resultType.type }

          return toScheme(newType)
        })
        .mapLeft(e => {
          throw new Error(`This should be impossible: Lambda variables not found: ${e.map(errorTreeToString)}`)
        })
    })

    this.addToResults(e.id, result)
    this.freeNames.pop()
  }

  //   Γ ⊢ e1: (t1, c1)  s = solve(c1)     s(Γ ∪ {n: t1}) ⊢ e2: (t2, c2)
  // ------------------------------------------------------------------------ (LET-OPDEF)
  //               Γ ⊢ val n = e1 { e2 }: (quantify(t2), c1 ∧ c2)
  exitLet(e: QuintLet) {
    if (this.errors.size !== 0) {
      return
    }

    // TODO: Occurs check on operator body to prevent recursion, see https://github.com/informalsystems/quint/issues/171

    this.addToResults(e.id, this.fetchResult(e.expr.id))
  }

  // TODO: On type app exit, add constraints for the type operators?
  // TODO: Need similar logic on exiting a type def (to create a scheme for a lambda) and
  exitOpDef(e: QuintOpDef) {
    if (this.errors.size !== 0) {
      return
    }

    this.fetchResult(e.expr.id).map(t => {
      this.addToResults(e.id, right(this.quantify(t.type)))
      if (e.typeAnnotation) {
        this.addTypeEqConstraint(t.type, e.typeAnnotation, e.id)
      }
    })
  }

  exitAssume(e: QuintAssume) {
    if (this.errors.size !== 0) {
      return
    }

    this.fetchResult(e.assumption.id).map(t => {
      this.addToResults(e.id, right(this.quantify(t.type)))
      this.constraints.push({ kind: 'eq', types: [t.type, { kind: 'bool' }], sourceId: e.id })
    })
  }

  private addToResults(exprId: bigint, result: Either<Error, TypeScheme>) {
    result
      .mapLeft(err => this.errors.set(exprId, buildErrorTree(this.location, err)))
      .map(r => this.types.set(exprId, r))
  }

  private fetchResult(id: bigint): Either<ErrorTree, TypeScheme> {
    const successfulResult = this.types.get(id)
    const failedResult = this.errors.get(id)
    if (failedResult) {
      return left(failedResult)
    } else if (successfulResult) {
      return right(successfulResult)
    } else {
      throw new Error(`Couldn't find any result for id ${id} while ${this.location}`)
    }
  }

  private solveConstraints(): Either<void, Substitutions> {
    const constraint: Constraint = { kind: 'conjunction', constraints: this.constraints, sourceId: 0n }

    // Remove solved constraints
    this.constraints = []

    return this.solvingFunction(this.table, constraint)
      .mapLeft(errors => errors.forEach((err, id) => this.errors.set(id, err)))
      .map(subs => {
        // For every free name we are binding in the substitutions, the names occurring in the value of the substitution
        // have to become free as well.
        this.addBindingsToFreeNames(subs)

        // Apply substitution to environment
        // FIXME: We have to figure out the scope of the constraints/substitutions
        // https://github.com/informalsystems/quint/issues/690
        this.types.forEach((oldScheme, id) => {
          const newType = applySubstitution(this.table, subs, oldScheme.type)
          const newScheme: TypeScheme = this.quantify(newType)
          this.addToResults(id, right(newScheme))
        })

        return subs
      })
  }

  // If there is a builtin called `name`, compute a new instance of its type scheme,
  // otherwise, compute a new instance of the scheme previously computed for `id`
  private typeForName(name: string, id: bigint, arity: number): Either<ErrorTree, QuintType> {
    // Assumes a valid number of arguments

    if (this.builtinSignatures.has(name)) {
      const signatureFunction = this.builtinSignatures.get(name)!
      const signature = signatureFunction(arity)
      return right(this.newInstance(signature))
    } else {
      return this.typeForId(id).mapLeft(
        (child: ErrorTree): ErrorTree => ({
          location: `looking up type for ${name}`,
          children: [child],
        })
      )
    }
  }

  // Fetch a new instance of the scheme previously computed for `id`
  private typeForId(id: bigint): Either<ErrorTree, QuintType> {
    const def = this.table.get(id)

    if (!def) {
      return left(buildErrorLeaf(this.location, `no entry for id ${id} in lookup table`))
    }
    if (!def.id) {
      return left(buildErrorLeaf(this.location, `no id for lookup table entry for  ${id}`))
    }

    // FIXME: We have to check if the annotation is too general for var and consts as well
    // https://github.com/informalsystems/quint/issues/691
    return this.fetchResult(def.id).map(t => {
      const inferredType = this.newInstance(t)
      if (def.typeAnnotation) {
        this.addTypeEqConstraint(inferredType, def.typeAnnotation, def.id)
      }
      return inferredType
    })
  }

  private addTypeEqConstraint(t1: QuintType, t2: QuintType, sourceId: bigint) {
    const t1Resolved = t1.kind === 'app' ? this.resolveTypeApp(t1) : t1
    const t2Resolved = t2.kind === 'app' ? this.resolveTypeApp(t2) : t2
    this.constraints.push({
      kind: 'eq',
      types: [t1Resolved, t2Resolved],
      sourceId,
    })
  }

  private resolveTypeApp(t: QuintAppType): QuintType {
    const typeDef = this.table.get(t.ctor.id!)! // TODO
    if (typeDef.kind !== 'typedef' || !typeDef.type) {
      fail(`invalid kind looked up for constructor of type application with id ${t.ctor.id} `)
    }
    const { params, scheme } = this.quantifyTypeDef(typeDef as QuintTypeAlias)
    zip(params, t.args).forEach(([param, arg]) =>
      this.constraints.push({
        kind: 'eq',
        types: [param, arg],
        sourceId: arg.id!,
      })
    )
    return scheme.type
  }

  private newInstance(t: TypeScheme): QuintType {
    const typeNames = Array.from(t.typeVariables)
    const rowNames = Array.from(t.rowVariables)

    const typeSubs: Substitutions = typeNames.map(name => {
      return { kind: 'type', name: name, value: { kind: 'var', name: this.freshVarGenerator.freshVar('_t') } }
    })

    const rowSubs: Substitutions = rowNames.map(name => {
      return { kind: 'row', name: name, value: { kind: 'var', name: this.freshVarGenerator.freshVar('_t') } }
    })

    const subs = compose(this.table, typeSubs, rowSubs)
    return applySubstitution(this.table, subs, t.type)
  }

  private currentFreeNames(): { typeVariables: Set<string>; rowVariables: Set<string> } {
    return (
      this.freeNames[this.freeNames.length - 1] ?? {
        typeVariables: new Set(),
        rowVariables: new Set(),
      }
    )
  }

  // Converts a type definition into a TypeScheme with all fresh variables, and
  // a list of params providing the fresh type variables corresponding to the
  // order they are specified in the type declaration. This is binding the type
  // parameters of a declared polymorphic type via universal quantification.
  //
  // E.g., the type definition
  //
  //   type Result[ok, err] = Ok(ok) | Err(err)
  //
  // Will produce the result
  //
  //   { params: [fresh_ok, fresh_err],
  //     scheme: ∀(fresh_ok,fresh_err). Ok(fresh_ok) | Err(fresh_err)
  //   }
  private quantifyTypeDef(typeDef: QuintTypeAlias): { params: QuintVarType[]; scheme: TypeScheme } {
    if (!typeDef.params || typeDef.params.length === 0) {
      return { params: [], scheme: this.quantify(typeDef.type) }
    }

    // Coordinates parameter names with their corresponding fresh variables
    const varsMap: Map<string, string> = new Map(
      typeDef.params.map(param => [param, this.freshVarGenerator.freshVar(param)])
    )

    // Parsing guarantees that every variable in a type def is in the params
    const typeWithFreshVars = mapTypeVarNames(n => varsMap.get(n)!, typeDef.type)
    const params: QuintVarType[] = [...varsMap.values()].map(name => ({ kind: 'var', name }))

    return { scheme: this.quantify(typeWithFreshVars), params }
  }

  private quantify(type: QuintType): TypeScheme {
    const freeNames = this.currentFreeNames()
    const nonFreeNames = {
      typeVariables: new Set([...typeNames(type).typeVariables].filter(name => !freeNames.typeVariables.has(name))),
      rowVariables: new Set([...typeNames(type).rowVariables].filter(name => !freeNames.rowVariables.has(name))),
    }
    return { ...nonFreeNames, type }
  }

  private addBindingsToFreeNames(substitutions: Substitutions) {
    // Assumes substitutions are topologically sorted, i.e. [ t0 |-> (t1, t2), t1 |-> (t3, t4) ]
    substitutions.forEach(s => {
      switch (s.kind) {
        case 'type':
          this.freeNames
            .filter(free => free.typeVariables.has(s.name))
            .forEach(free => {
              const names = typeNames(s.value)
              names.typeVariables.forEach(v => free.typeVariables.add(v))
              names.rowVariables.forEach(v => free.rowVariables.add(v))
            })
          return
        case 'row':
          this.freeNames
            .filter(free => free.rowVariables.has(s.name))
            .forEach(free => rowNames(s.value).forEach(v => free.rowVariables.add(v)))
          return
      }
    })
  }
}

function checkAnnotationGenerality(
  subs: Substitutions,
  typeAnnotation: QuintType | undefined
): Either<ErrorTree, Substitutions> {
  if (!typeAnnotation) {
    return right(subs)
  }

  // Find type and row variables in the annotation that are bound to non-variable types in the substitutions.
  // This indicates that they are inferred to have a concrete type.
  const names = typeNames(typeAnnotation)
  const tooGeneralTypes = subs.filter(
    s => s.kind === 'type' && s.value.kind !== 'var' && names.typeVariables.has(s.name)
  )
  const tooGeneralRows = subs.filter(s => s.kind === 'row' && s.value.kind !== 'var' && names.rowVariables.has(s.name))

  const errors = [...tooGeneralTypes, ...tooGeneralRows].map(s => {
    const expected = s.kind === 'type' ? typeToString(s.value) : rowToString(s.value)
    return buildErrorLeaf(
      `Checking variable ${s.name}`,
      `Type annotation is too general: ${s.name} should be ${expected}`
    )
  })

  if (errors.length > 0) {
    return left(buildErrorTree(`Checking type annotation ${typeToString(typeAnnotation)}`, errors))
  } else {
    return right(subs)
  }
}

function mapTypeVarNames(f: (_: string) => string, t: QuintType): QuintType {
  const transformer = new TypeVariableNameMapper(f)
  return transformType(transformer, t)
}

class TypeVariableNameMapper implements IRTransformer {
  private mapper: (_: string) => string

  constructor(f: (_: string) => string) {
    this.mapper = f
  }

  exitVar(t: QuintVar): QuintVar {
    return { ...t, name: this.mapper(t.name) }
  }

  exitRow(r: Row): Row {
    return r.kind === 'var' ? { ...r, name: this.mapper(r.name) } : r
  }
}
