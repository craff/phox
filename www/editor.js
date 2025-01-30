var main = false;

function ensureTextNode(node) {
    const elts = node.querySelectorAll("span");
    for (elt of elts) {
	if (elt.childNodes.length == 0) {
	    elt.appendChild(document.createTextNode(''));
	}
    }
}

let top_commands = new RegExp ("\\b((" +
    ["Cst", "Import", "Use", "Sort",
     "new_intro", "new_elim", "new_rewrite",
     "add_path", "author", "cd",
     "claim", "close_def", "def", "del", "documents",
     "depend", "elim_after_intro", "export",
     "edel", "eshow", "flag", "goal", "include",
     "institute", "path", "print_sort", "priority",
     "quit", "save", "search", "tex", "tex_syntax", "title",
     "proposition", "prop", "lemma", "lem", "fact", "corollary", "cor",
     "theorem", "theo"].join(")|(") + "))\\b", "g");

let proof_commands = new RegExp ("\\b((" +
    ["abort", "absurd", "apply", "axiom", "constraints",
     "elim", "from", "goals", "intros", "intro", "instance",
     "local", "lefts", "left", "next", "rewrite", "rewrite_hyp",
     "rename", "rmh", "trivial", "slh", "use", "undo", "unfold",
     "unfold_hyp"].join(")|(") + "))\\b", "g");

// XMLEscape reserverd characters
function XMLEscape(sValue, bUseApos) {
  var sval="";
  for(var idx=0; idx < sValue.length; idx++) {
    var c = sValue.charAt(idx);
    if      (c == '<') sval += "&lt;";
    else if (c == '>') sval += "&gt;";
    else sval += c;
  }
  return sval;
}

function search_end(s,from,re) {
    let start = s.slice(from).search(re);
    if (start >= 0) {
	start += from;
	const end = start + s.slice(start).match(re)[0].length;
	return [start, end];
    } else {
	return [s.length, s.length];
    }
}

function replace_syntax(s) {
    let res = "";
    let index = 0;
    let start = 0;
    let end = 0;
    while (([start, end] = search_end(s, index, /[\\][^\\s\n]+[\\]/))[0] < s.length) {
        res += s.substring(index, start);
        index = start;
        const matched = s.substring(index+1,end-1);
        switch (matched) {
        case "forall":
        case "all":
            res += "∀"; break;
        case "exists":
            res += "∃"; break;
        case "wedge":
        case "&":
        case "and":
        case "land":
            res += "∧"; break;
        case "vee":
        case "or":
        case "lor":
            res += "∨"; break;
        case "to":
	case "->":
            res += "→"; break;
        case "not":
        case "neg":
            res += "¬"; break;
        case "cup":
        case "union":
            res += "∪"; break;
        case "cap":
        case "inter":
            res += "∩"; break;
        case "subset":
            res += "⊂"; break;
        case "in":
            res += "∈"; break;
        case "notin":
            res += "∉"; break;
        case "times":
        case "*":
            res += "×"; break;
        case "!=":
        case "neq":
            res += "≠"; break;
        case "<=":
	case "leq":
            res += "≤"; break;
        case ">=":
        case "geq":
            res += "≥"; break;
        default:
            res += s.substring(index,end);
        }
        index = end;
    }
    res += s.substring(index, s.length);
    return(res);
}

// Syntax highlight for JS
const phox = (node,pos=null) => {
    function subst(s, dest) {
	dest.innerHTML="";
	let current = 0;
	let diff = 0;
	while (current < s.length) {
	    let [index, end] = search_end(s,current,/\n/);
	    const div = document.createElement("div");
	    const line = s.substring(current,index);
	    let current2 = 0;
            let nospan = true;
	    while(current2 < line.length) {
		let [index2, end2] = search_end(line,current2,/[.](\s|$)/);
		let start = line.substring(current2, end2);
		const span = document.createElement("span");
		start = XMLEscape(start);
		start = start.replace(top_commands,"<strong>$1</strong>");
		start = start.replace(proof_commands,"<em>$1</em>");
		const old   = start.length;
		start = replace_syntax(start);
		if (pos && pos.col > current2) diff += old - start.length;
		span.innerHTML = start;
		div.appendChild(span);
		current2 = end2;
                nospan = false;
	    }
            if (nospan) {
	        const span = document.createElement("span");
		span.innerHTML = "<br>";
	        span.appendChild(document.createTextNode(""));
	        div.appendChild(span);
            }
	    dest.appendChild(div);
	    current=end;
	}
        if (pos) pos.col -= diff;
    }

    if (node && node.childNodes.length > 0 && node.childNodes[0].contentEditable == "false") {
	let i = 0;
	while (i < node.childNodes.length &&
               node.childNodes[i].contentEditable == "false") {
            i++;
        }
        if (i >= node.childNodes.length) return;
	while (elt = node.childNodes[i]) {
	    s += elt.textContent;
	    node.removeChild(elt);
	}
	const new_node = document.createElement("div");
	const diff = subst(s,new_node);
	if (new_node.childNodes.length > 0) {
	    while (elt = new_node.firstChild.firstChild) {
		new_node.firstChild.removeChild(elt);
		node.appendChild(elt);
	    }
	}
	new_node.removeChild(new_node.firstChild);
	if (new_node.childNodes.length > 0) {
	    node.parentNode.insertBefore(new_node, node.nextSibling);
	    new_node.replaceWith(new_node.childNodes);
	}
	return diff;
    } else if (node && node.innerText && (node.innerText.length > 0)) {
	const diff = subst(node.innerText, node);
	node.replaceWith(...node.childNodes);
	return diff;
    }
};


const editor = (el, highlight=phox, tab = '  ') => {
    const getLine = (node) => {
	let prev = null;
	while (node && node.tagName !== "DIV") {
	    prev = node;
	    node = node.parentNode;
	}
	return { line: node, span: prev };
    };

    const getSpan = (node) => {
	while (node && node.tagName !== "SPAN") {
	    node = node.parentNode;
	}
	return node;
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
	const line = getLineNumber(node.line);
	const range = sel.getRangeAt(0);
	const prefix = range.cloneRange();
	prefix.selectNodeContents(node.line);
	prefix.setEnd(range.endContainer, range.endOffset);
	const col = prefix.toString().length;
        const atEof = prefix.endOffset == prefix.endContainer.textContent.length
              && getSpan(prefix.endContainer) && !getSpan(prefix.endContainer).nextSibling;
	return {line: line, span:node.span, col: col, atEof: atEof}
    };

    el.caret = caret;

    const setCaretOffset = (pos, parent, top) => {
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
	line = el.children[pos.line];
	if (line) setCaretOffset(pos.col, line, true);
    };

    const insertLine = (txt) => {
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

    const highlightAt = (pos) => {
	const line = el.children[pos.line];
	highlight(line, pos);
    };

    const getContent= () =>  {
	const el = document.getElementsByClassName('editor')[0]; // assume one editor
	let r = "";
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
	} /*else if (e.which == 13) {
	    const pos = caret();
            insertLine(pos.atEof?"\n\n":"\n");
	    highlightAt({line: pos.line, col: 0, span:null});
            setCaret({line: pos.line+1, col: 0});
            e.preventDefault();
	} */

    });

    el.addEventListener('keyup', e => {
	if (e.which != 16 && e.which != 13 &&
            e.which != 91 && (e.which < 33 || e.which > 40)) {
	    let pos = caret();
	    highlightAt(pos);
	    setCaret(pos);
	}
    });

    el.setContent = (text => {
	el.innerHTML = '<div><span> </span></div>';
	setCaret({line: 0, col: 0});
	insertLine(text);
	highlightAt(caret());
    });

    el.addEventListener('paste', e => {
	const data = e.clipboardData;
	const text = data.getData("text");
	insertLine(text);
	highlightAt(caret());
	e.preventDefault();
    });

    el.addEventListener('copy', e => {
	const el = document.getElementsByClassName('editor')[0]; // assume one editor
	let r = "";
	const sel = window.getSelection();
	const range = sel.getRangeAt(0);
        const node1 = getLine(range.startContainer);
        const line1 = getLineNumber(node1.line);
        const node2 = getLine(range.endContainer);
        const line2 = getLineNumber(node2.line);

        if (line1 == line2) {
            r = range.toString();
        } else {
            const prefix = document.createRange();
            prefix.setStart(node1.line, 0);
            prefix.setEnd(range.startContainer, range.startOffset);
            r += node1.line.textContent.substring(prefix.toString().length) + '\n';
	    for (let i = line1 + 1; i < line2; i++) {
	        r += el.children[i].textContent + '\n';
	    }
            prefix.setStart(node2.line, 0);
            prefix.setEnd(range.endContainer, range.endOffset);
            r += prefix.toString();
        }
	e.clipboardData.setData("text/plain", r);
        e.preventDefault();
    });

};
