import 'mocha';
import { assert } from 'chai';
import { readFileSync } from 'fs';
import { resolve } from 'path';
import { ErrorMessage, parsePhase1, ParseResult } from "../src/parser/tntParserFrontend";
import { TntDef } from "../src/parser/tntIr";

function readTest(name: string): string {
	const p = resolve(__dirname, '../testFixture', name + ".tnt")
	return readFileSync(p).toString('utf8')
}

describe('parse modules', () => {
	it('parse empty module', () => {
	  const result = parsePhase1(readTest("_0001emptyModule"));
	  const module = { id: 1n, name: "empty", extends: [], defs: [] }
	  assert.deepEqual(result, {kind: 'ok', module: module}, "expected ok")
	}); 

	it('error message on error in module unit', () => {
		const result = parsePhase1(readTest("_0002emptyWithError"));
		const msg: ErrorMessage = {
			explanation: "TNT001: expected a const, var, def, typedef, etc.",
			 lineNo: 4,
			 charNo: 0,
			 length: 3
		};
		const expected: ParseResult = { kind: "error", messages: [ msg ] };
		assert.deepEqual(result, expected, "expected error");
	}); 

	it('parse constants', () => {
	  const result = parsePhase1(readTest("_0003consts"));
	  // const N: int
	  const constN: TntDef = { id: 1n, kind: "const", name: "N", typeTag: { kind: "untyped", paramArities: [] } }
	  // const MySet: set(int)
	  const constMySet: TntDef = { id: 2n, kind: "const", name: "MySet",
	  	typeTag: { kind: "set", elem: { kind: "int" } } }
	  // const MySeq: seq(int)
	  const constMySeq: TntDef = { id: 3n, kind: "const", name: "MySeq",
	  	typeTag: { kind: "seq", elem: { kind: "bool" } } }
	  // const MyFun: int -> str
	  const constMyFun: TntDef = { id: 4n, kind: "const", name: "MyFun",
	  	typeTag: { kind: "fun", arg: { kind: "int" }, res: { kind: "str" } } }
	  // const MyFun: (int -> str) -> bool
	  const constMyFunFun: TntDef = { id: 5n, kind: "const", name: "MyFunFun",
	  	typeTag: { kind: "fun",
		  		   arg: { kind: "fun", arg: { kind: "int" }, res: { kind: "str" } },
				   res: { kind: "bool" }
				}}
	  // const MyOper: (int, str) => bool
	  const constMyOper: TntDef = { id: 6n, kind: "const", name: "MyOper",
	  	typeTag: { kind: "oper", args: [{ kind: "int" }, {kind: "str"}], res: { kind: "bool" } } }
	  // const MyTuple: (int, bool, str)
	  const constMyTuple: TntDef = { id: 7n, kind: "const", name: "MyTuple",
	  	typeTag: { kind: "tuple", elems: [ { kind: "int" }, {kind: "bool"}, { kind: "str" } ] } }
	  // the module that contains all these constants
	  const module = { id: 8n, name: "withConsts", extends: [],
	  	defs: [ constN, constMySet, constMySeq, constMyFun,
				constMyFunFun, constMyOper, constMyTuple ] }

	  assert.deepEqual(result, { kind: 'ok', module: module }, "expected ok")
	}); 

	it('parse record types in constants', () => {
	  const result = parsePhase1(readTest("_0004constRecords"));
	  // const MyRecord: { "i": int, "b": bool, "s": str }
	  const constMyRecord: TntDef = { id: 1n, kind: "const", name: "MyRecord",
	  	typeTag: { kind: "record",
		  		   fields: [ { fieldName: "i", fieldType: { kind: "int" } },
					         { fieldName: "b", fieldType: { kind: "bool"} },
							 { fieldName: "s", fieldType: { kind: "str" } } ] } }

	  // disjoint unions are the most complex type in our type system
	  const constMyUnion: TntDef =
	  	{ id: 2n, kind: "const", name: "MyUnion",
		  typeTag: {
			kind: "union", tag: "type",
			records: [
				{
					tagValue: "circle",
				  	fields: [ {fieldName: "radius", fieldType: { kind: "int" } } ]
				},
				{
					tagValue: "rectangle",
				  	fields: [
					  {fieldName: "width", fieldType: { kind: "int" } },
					  {fieldName: "height", fieldType: { kind: "int" } },
					]
				},
				{
					tagValue: "dog",
				  	fields: [ {fieldName: "name", fieldType: { kind: "str" } } ]
				},
			]
		  }
		}

	  // the module that contains all these constants
	  const module = { id: 3n, name: "withConsts", extends: [],
	  	defs: [ constMyRecord, constMyUnion ] }

	  assert.deepEqual(result, { kind: 'ok', module: module }, "expected ok")
	});

	it('error message in malformed disjoint union', () => {
		const result = parsePhase1(readTest("_0005constRecordsError"));
		const msg: ErrorMessage = {
			explanation: "TNT011: Records in disjoint union have different tag fields: type and kind",
			 lineNo: 5,
			 charNo: 2,
			 length: 1
		};
		const expected: ParseResult = { kind: "error", messages: [ msg ] };
		assert.deepEqual(result, expected, "expected error");
	}); 
});
