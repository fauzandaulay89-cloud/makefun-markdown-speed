// Driver for the make.fun markdown-render-speed-02 bounty: it takes
// every case from /input/cases.json, renders it with parse() from
// parse.js, and writes the resulting HTML strings, in order, to
// /output/html.json. Outside the grading container, the
// MAKEFUN_INPUT_DIR and MAKEFUN_OUTPUT_DIR environment variables
// stand in for /input and /output.
import * as fs from 'node:fs';
import * as path from 'node:path';
import { parse } from './parse.js';
const inputDir = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const outputDir = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const cases = JSON.parse(fs.readFileSync(path.join(inputDir, 'cases.json'), 'utf8'));
const rendered = [];
for (const c of cases) rendered.push(parse(c.markdown));
fs.mkdirSync(outputDir, { recursive: true });
fs.writeFileSync(path.join(outputDir, 'html.json'), JSON.stringify(rendered));
