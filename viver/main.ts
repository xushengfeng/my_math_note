import {
	view,
	initDKH,
	addClass,
	type ElType,
	textarea,
	pText,
	button,
} from "dkh-ui";
import rehypeRaw from "rehype-raw";
import rehypeStringify from "rehype-stringify";
import remarkFrontmatter from "remark-frontmatter";
import remarkGfm from "remark-gfm";
import remarkParse from "remark-parse";
import remarkRehype from "remark-rehype";
import { unified } from "unified";
import type { Root, Paragraph } from "mdast";
import type { Schema } from "../data.d.ts";

async function init() {
	const _data = (await (await fetch("./data.json")).json()) as Schema;
	console.log(_data);
	data = _data;
	bookListEl.clear();
	bookListEl.add(
		_data.books.map((item) => {
			return view()
				.add(item.name)
				.on("click", () => {
					console.log(item);
					showBook(item.id);
				});
		}),
	);
	const { bid, cid } = Object.fromEntries(new URLSearchParams(location.search));
	showBook(bid || Object.values(_data.books).at(0)?.id || "");
	if (cid) {
		showText(cid);
	}
}

function updateURL(op: { bid?: string; cid?: string }) {
	const l = new URL(location.href);
	const s = new URLSearchParams(l.search);
	if (op.bid) s.set("bid", op.bid);
	if (op.cid) s.set("cid", op.cid);
	l.search = s.toString();
	history.pushState({}, "", l.href);
}

function showBook(id: string) {
	if (!id) return;
	const book = data.books.find((b) => b.id === id);
	if (!book) {
		contentEl.clear().add("Book not found");
		return;
	}
	updateURL({ bid: id });
	contentEl.clear();
	sideEl.clear().add(
		book.chapter.map((i) => {
			const n = data.text.find((x) => i === x.id);
			return view()
				.add(n ? n.name : "Unknown")
				.on("click", () => {
					showText(i);
				});
		}),
	);
}

async function showText(id: string) {
	const text = data.text.find((x) => id === x.id);
	if (!text) {
		contentEl.clear().add("Text not found");
		return;
	}
	const path = text.path;
	console.log(path);
	updateURL({ cid: text.id });
	const fdata = await (await fetch(path)).text();
	const file = await processor.process(fdata);
	contentEl.clear();
	contentEl.el.innerHTML = file.value.toString();
	renderLeanCode();
}

async function renderLeanCode() {
	const els = contentEl.queryAll("div[data-pid], span[data-pid]");
	for (const _el of els) {
		const el = _el as ElType<HTMLElement>;
		el.clear();
		const url = el.el.getAttribute("data-pid")!;
		const o = codeUrlParse(url);
		renderLeanCode2(el, o);
	}
}

function codeUrlParse(url: string) {
	const [id, x] = url.split("?");
	const o: {
		id: string;
		answer?: boolean;
		hide?: boolean;
		from?: string;
		to?: string;
	} = { id: id! };
	const l = x?.split("&") || [];
	for (const i of l) {
		if (!i) continue;
		const [k, v] = i.split("=");
		if (k)
			// @ts-expect-error
			o[k] = v || true;
	}
	return o;
}

async function renderLeanCode2(
	el: ElType<HTMLElement>,
	o: ReturnType<typeof codeUrlParse>,
) {
	const q = data.qa.find((i) => i.id === o.id);
	if (!q) {
		el.add(`找不到${o.id}`);
		return;
	}
	const f = await (await fetch(q.path)).text();
	const lines = f.split("\n");

	const from = o.from ? Number(o.from) - 1 : 0;
	const to = o.to ? Number(o.to) : lines.length;

	const f2 = lines.slice(from, to).join("\n");

	const textEl = pText().sv(f2);
	if (o.hide) {
		textEl.style({ display: "none" });
		const b = button().add("::").style({ fontFamily: "monospace" });
		b.on("click", () => {
			if (textEl.el.style.display === "none") textEl.style({ display: "" });
			else textEl.style({ display: "none" });
		});
		el.add(b).add(textEl);
	} else {
		el.add(textEl);
	}
}

// 自定义插件：处理 [[p:id]] 语法
function customPlugin() {
	return (tree: Root) => {
		// 遍历所有节点
		tree.children.forEach((node) => {
			if (node.type === "paragraph") {
				processParagraph(node);
			} else if (node.type === "list") {
				// 处理列表中的段落
				node.children.forEach((listItem) => {
					if (listItem.children && listItem.children.length > 0) {
						listItem.children.forEach((itemNode) => {
							if (itemNode.type === "paragraph") {
								processParagraph(itemNode);
							}
						});
					}
				});
			}
		});
	};
}

// 处理段落节点
function processParagraph(node: Paragraph) {
	if (!node.children) return;

	const newChildren: Paragraph["children"] = [];

	const rg = /\[\[p:([^\]]+)\]\]/g;

	// 段落模式
	if (node.children.length === 1 && node.children[0]?.type === "text") {
		const f = node.children[0].value;
		const m = f.match(rg);
		if (m && m[0].length === f.length) {
			node.children = [
				{
					type: "html",
					value: `<div data-pid="${m[1]}">${m[1]}</div>`,
				},
			];
			return;
		}
	}

	node.children.forEach((child) => {
		if (child.type === "text" && child.value) {
			// 使用正则表达式匹配 [[p:id]] 模式
			const matches = Array.from(child.value.matchAll(rg));

			if (matches.length > 0) {
				let lastIndex = 0;

				for (const match of matches) {
					// 添加匹配前的文本
					if (match.index! > lastIndex) {
						newChildren.push({
							type: "text",
							value: child.value.substring(lastIndex, match.index!),
						});
					}

					// 添加自定义元素节点
					newChildren.push({
						type: "html",
						value: `<span data-pid="${match[1]}">${match[1]}</span>`,
					});

					lastIndex = match.index! + match[0].length;
				}

				// 添加剩余的文本
				if (lastIndex < child.value.length) {
					newChildren.push({
						type: "text",
						value: child.value.substring(lastIndex),
					});
				}
			} else {
				// 没有匹配，添加整个文本
				newChildren.push(child);
			}
		} else {
			// 如果不是文本节点，直接添加
			newChildren.push(child);
		}
	});

	// 更新节点的子节点
	node.children = newChildren;
}

let data: Schema = { meta: {}, books: [], qa: [], text: [] };

const mainEl = view().addInto();

const bookListEl = view().addInto(mainEl);
const contentElP = view().addInto(mainEl);
const sideEl = view().addInto(contentElP);
const contentEl = view()
	.addInto(contentElP)
	.class(
		addClass(
			{
				paddingInline: "8em",
				paddingBlockEnd: "60vh",
			},
			{
				"& h1": {
					fontWeight: "bolder",
					fontSize: "2em",
					marginBlock: "1em",
				},
				"& h2": {
					fontWeight: "bold",
					fontSize: "1.4em",
				},
				"& code": {
					paddingInline: "2px",
					background: "#eee",
				},
				"& p": {
					marginBlock: "1em",
				},
			},
		),
	);

const processor = unified()
	.use(remarkParse)
	.use(remarkFrontmatter)
	.use(customPlugin)
	.use(remarkGfm)
	.use(remarkRehype, { allowDangerousHtml: true })
	.use(rehypeRaw)
	.use(rehypeStringify);

initDKH({ pureStyle: true });

init();
