var main = false;

function ensureTextNode(node) {
    const elts = node.querySelectorAll("span");
    for (elt of elts) {
	if (elt.childNodes.length == 0) {
	    elt.appendChild(document.createTextNode(''));
	}
    }
}

// Syntax highlight for JS
const phox = node => {
    function subst(s) {
	s = s.replace(/\b(goal|save)(?=([^\w]|$))/g,"<strong>$1</strong>");
	console.log('phox: ', JSON.stringify(s));
	s = s.replace(/\n+$/g,'');
	s = '<div><span>'
	    + s.replace(/\n/g,'</span></div><div><span>')
	    + '</span></div>';
	s = s.replace(/([.])(\s+)/g,"$1</span><span>$2");
	s.replace(/&nbsp;/g,' ');
	console.log(s);
	return s;
    }

    if (node.childNodes.length > 0 && node.childNodes[0].contentEditable == "false") {
	console.log(node);
	let i = 0;
	while (node.childNodes[i].contentEditable == "false") i++;
	let s = "";
	while (elt = node.childNodes[i]) {
	    s += elt.textContent;
	    console.log(s, elt, elt.innerText, elt.textContent);
	    node.removeChild(elt);
	}
	const new_node = document.createElement("div");
	const s0 = subst(s);
	new_node.innerHTML = s0;
	ensureTextNode(new_node);
	console.log(node, s0, new_node);
	if (new_node.childNodes.length > 0) {
	    while (elt = new_node.firstChild.firstChild) {
		console.log('append:', elt);
		new_node.firstChild.removeChild(elt);
		node.appendChild(elt);
	    }
	}
	new_node.removeChild(new_node.firstChild);
	if (new_node.childNodes.length > 0) {
	    node.parentNode.insertBefore(new_node, node.nextSibling);
	    new_node.replaceWith(new_node.childNodes);
	}
    } else if (node.innerText) {
	console.log(node, node.children, node.innertText);
	const s0 = subst(node.innerText);
	node.innerHTML = s0;
	ensureTextNode(node);
	node.replaceWith(...node.childNodes);
    }
};


const editor = (el, highlight=phox, tab = '  ') => {
    const getLine = (node) => {
	prev = null;
	while (node && node.tagName !== "DIV") {
	    prev = node;
	    node = node.parentNode;
	}
	return { line: node, span: prev };
    };

    const getLineNumber = (node) => {
	let i = 0;
	for (line of el.children) {
	    if (line == node) return i;
	    i++
	}
	return undefined;
    };

    const caret = () => {
	const sel = window.getSelection();
	let node = sel.focusNode;
	node = getLine(node);
	console.log(sel, node);
	const line = getLineNumber(node.line);
	const range = sel.getRangeAt(0);
	const prefix = range.cloneRange();
	prefix.selectNodeContents(node.line);
	prefix.setEnd(range.endContainer, range.endOffset);
	const col = prefix.toString().length;
	console.log(line, col);
	return {line: line, span:node.span, col: col}
    };

    el.caret = caret;

    const setCaretOffset = (pos, parent, top) => {
	console.log("setCaretOffset:",pos, parent, top)
	for (const node of parent.childNodes) {
	    if (node.nodeType == Node.TEXT_NODE) {
		if (node.length >= pos || (!node.nextSibling && top)) {
		    pos = Math.min(pos, node.length);
		    const range = document.createRange();
		    const sel = window.getSelection();
		    range.setStart(node, pos);
		    range.collapse(true);
		    sel.removeAllRanges();
		    sel.addRange(range);
		    return -1;
		} else {
		    pos = pos - node.length;
		}
	    } else {
		pos = setCaretOffset(pos, node, top && !node.nextSibling);
		if (pos < 0) {
		    return pos;
		}
	    }
	}
	return pos;
    };

    const setCaret = (pos, parent = el) => {
	console.log(pos.line,pos.col);
	line = el.children[pos.line];
	setCaretOffset(pos.col, line, true);
    };

    const insertLine = (txt) => {
	console.log("line:", txt);
	const sel = window.getSelection();
        range = sel.getRangeAt(0);
        range.deleteContents();
        range.insertNode( document.createTextNode(txt) );
    };

    const highlightAll = (parent = el) => {
	for (node of parent.childNodes) {
	    highlight(node);
	}
    };

    highlightAll(el);

    const highlightAt = (pos) => {
	const line = el.children[pos.line];
	highlight(line);
    };

    const getContent= () =>  {
	const el = document.getElementsByClassName('editor')[0]; // assume one editor
	r = "";
	for (const ch of el.children) {
	    r += ch.textContent + "\n";
	}
	return(r);
    };

    el.addEventListener('keydown', e => {
	if (e.which === 9) {
	    const pos = caret().col + tab.length;
	    const range = window.getSelection().getRangeAt(0);
	    range.deleteContents();
	    range.insertNode(document.createTextNode(tab));
	    e.preventDefault();
      } else if (e.which == 38) {
	    const pos = caret();
	    console.log(pos);
	    if (pos.line > 0) {
		setCaret({line: pos.line - 1, col: pos.col});
	    }
	    e.preventDefault();
      } else if (e.which == 40) {
	    const pos = caret();
	    console.log(pos);
	    if (pos.line < el.children.length - 1) {
		setCaret({line: pos.line + 1, col: pos.col});
	    }
	    e.preventDefault();
      }
    });

    el.addEventListener('keyup', e => {
	console.log('key: ', e.which, caret());
	if (e.which != 16 && e.which != 91 && (e.which < 33 || e.which > 40)) {
	    let pos = caret();
	    highlightAt(pos);
	    setCaret(pos);
	    if (e.which == 13) {
		highlightAt({line: pos.line - 1, col: 0, span:null});
	    }
	}
    });

    el.setContent = (text => {
	el.innerHTML = '<div><span> </span></div>';
	setCaret({line: 0, pos: 0});
	insertLine(text);
	highlightAt(caret());
    });

    el.addEventListener('paste', e => {
	const data = e.clipboardData;
	const text = data.getData("text");
	el.setContent(text);
	e.preventDefault();
    });
};
