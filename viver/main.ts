import { view, initDKH, addClass } from "dkh-ui";
import rehypeRaw from "rehype-raw";
import rehypeStringify from "rehype-stringify";
import remarkFrontmatter from "remark-frontmatter";
import remarkGfm from "remark-gfm";
import remarkParse from "remark-parse";
import remarkRehype from "remark-rehype";
import { unified } from "unified";

async function init() {
	const _data = await (await fetch("./data.json")).json();
	console.log(_data);
	data = _data;
	bookListEl.clear();
	bookListEl.add(
		_data.books.map((item: any) => {
			return view()
				.add(item.name)
				.on("click", () => {
					console.log(item);
					showBook(item.id);
				});
		}),
	);
	const { bid, cid } = Object.fromEntries(new URLSearchParams(location.search));
	showBook(bid || _data.books[0].id);
	if (cid) {
		const n = data.text.find((x: any) => cid === x.id);
		showText(n);
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
	const book = data.books.find((b: any) => b.id === id);
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
					showText(n);
				});
		}),
	);
}

async function showText(text: any) {
	const path = text.path;
	console.log(path);
	updateURL({ cid: text.id });
	const data = await (await fetch(path)).text();
	const file = await processor.process(data);
	contentEl.clear();
	contentEl.el.innerHTML = file.value.toString();
}

let data: any = null;

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
	.use(remarkGfm)
	.use(remarkRehype, { allowDangerousHtml: true })
	.use(rehypeRaw)
	.use(rehypeStringify);

initDKH({ pureStyle: true });

init();
