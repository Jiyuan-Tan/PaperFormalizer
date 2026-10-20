from pathlib import Path
import re, json, sys

def uncomment(s):
    out=[]; start=0
    outer=re.compile(r'/\-|--|"')
    inner=re.compile(r'/\-|-\/')
    string=re.compile(r'\\.|"')
    while m:=outer.search(s,start):
        out.append(s[start:m.start()])
        if m[0]=='--':
            end=s.find('\n',m.end()); end=len(s) if end<0 else end
        elif m[0]=='/-':
            depth=1; end=m.end()
            while depth:
                t=inner.search(s,end)
                if t is None: raise ValueError('Unclosed comment')
                depth += 1 if t[0]=='/-' else -1
                end=t.end()
        else:
            end=m.end()
            while t:=string.search(s,end):
                end=t.end()
                if t[0]=='"': break
        out.append(' ' + '\n'*s[m.start():end].count('\n'))
        start=end
    out.append(s[start:])
    return ''.join(out)

def names(root):
    result={}; placeholder=[]
    for p in sorted(root.rglob('*.lean')):
        s=uncomment(p.read_text())
        for match in re.finditer(r'\bsorry\b|\badmit\b|^[ \t]*axiom\b',s,re.M):
            placeholder.append(f'{p}:{s[:match.start()].count(chr(10))+1}')
        ns=''; stack=[]
        for line in s.splitlines():
            m=re.match(r'^\s*(?:(?:public|private|meta|noncomputable)\s+)*(namespace|section|end)\b\s*(\S*)',line)
            if m:
                kind,n=m.groups()
                if kind=='namespace':
                    stack.append((kind, ns))
                    ns=n.removeprefix('_root_.') if n.startswith('_root_.') else '.'.join(filter(None,[ns,n]))
                elif kind=='section': stack.append((kind,ns))
                elif stack: _,ns=stack.pop()
            m=re.match(r'^\s*(?:@\[.*?\]\s*)*(?:(?:public|private|protected|meta|noncomputable|unsafe|partial|local|scoped)\s+)*(?:theorem|lemma|def|abbrev|structure|class|inductive|opaque|axiom|instance)\s+([\w.\'\u0080-\uffff]+)',line)
            if m:
                n=m.group(1)
                n=n.removeprefix('_root_.') if n.startswith('_root_.') else '.'.join(filter(None,[ns,n]))
                result.setdefault(n,[]).append(str(p))
    return result,placeholder

if __name__=='__main__':
    a,pa=names(Path(sys.argv[1])); b,pb=names(Path(sys.argv[2]))
    common=sorted(a.keys()&b.keys())
    print('Authored named declaration candidates:',len(a),len(b))
    for n in common: print(n, a[n], b[n], sep='\n  ')
    print('StatLean proof placeholders outside comments/strings:',pa)
    Path('source-name-candidates.json').write_text(json.dumps({'statlean':a,'causalean':b,'common':common},indent=2))
