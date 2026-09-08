"""Refresh exact identity and export complete/source-only patches on exact base.
Uses isolated Git indexes inside this worktree; never modifies the real index.
No compiler, scorer, submission, protected edits or sibling worktree.
"""
import hashlib,json,os,subprocess,tempfile
from pathlib import Path
from repair_complements import S,HERE,BASE,ORIGINAL,build
from integrate_complements import snapshot,W
from evm import decode

def main():
    old=bytes.fromhex(snapshot()['bytecode.hex']);new,pm,im,_,_=build(old)
    assert new==bytes.fromhex((S/'bytecode.hex').read_text())
    original_identity=W/'artifacts/pr776-before-complements-identity.json'
    if not original_identity.exists():
        data=json.loads((HERE/'identity.json').read_text());assert data['sha256']==ORIGINAL
        original_identity.write_text(json.dumps(data,indent=2)+'\n')
    identity=json.loads(original_identity.read_text())
    identity.update(base=BASE,sha256=hashlib.sha256(new).hexdigest(),bytes=len(new),instructions=len(decode(new)),compiled=False,eligible_for_hosted_source=True)
    identity.pop('eligible',None)
    identity['labels']={k:pm[v] for k,v in identity['labels'].items()}
    for item in identity['boundaries'].values():item['pc']=pm[item['pc']]
    (HERE/'identity.json').write_text(json.dumps(identity,indent=2)+'\n')
    art=W/'artifacts'
    def git(*args,env=None):return subprocess.check_output(['git',*args],cwd=W,env=env)
    assert git('rev-parse','HEAD').decode().strip()==BASE
    changes=git('diff','--name-only',BASE).decode().splitlines()
    assert all(p.startswith('Challenge/Modexp/Submission/') for p in changes),changes
    assert not any(p.is_symlink() for p in S.rglob('*'))
    exports={}
    for kind in ('source','complete'):
        with tempfile.TemporaryDirectory(dir=art,prefix='.export-') as tmp:
            env=dict(os.environ,GIT_INDEX_FILE=str(Path(tmp)/'index'))
            git('read-tree',BASE,env=env)
            git('add','--','Challenge/Modexp/Submission',env=env)
            if kind=='complete':
                files=[str(p.relative_to(W)) for p in art.rglob('*') if p.is_file() and not any(x.startswith('.export-') for x in p.parts) and p.suffix!='.patch' and p.name!='complement-integration-receipt.json']
                git('add','-f','--',*files,env=env)
            tree=git('write-tree',env=env).decode().strip()
            patch=git('diff','--cached','--binary',BASE,env=env)
            dest=art/f'pr776-complements-{kind}.patch';dest.write_bytes(patch)
            files=git('diff','--cached','--name-only',BASE,env=env).decode().splitlines()
            git('read-tree',BASE,env=env)
            git('apply','--cached','--check',str(dest),env=env)
            git('apply','--cached',str(dest),env=env)
            assert git('write-tree',env=env).decode().strip()==tree
            exports[kind]={'path':str(dest),'sha256':hashlib.sha256(patch).hexdigest(),'bytes':len(patch),'files':len(files),'tree':tree,'apply_check':True,'applied_tree_matches':True}
    receipt={'base':BASE,'canonical_sha256':identity['sha256'],'bytes':len(new),'chunks':(len(new)+63)//64,'compiled':False,'source_integration':'complete uncompiled; hosted proof validation required','protected_edits':False,'source_patch_editable_only':True,'source_ancestry_eligible_at_frontier':True,'exports':exports,'official_score':None,'submissions_this_worker':0,'remaining':'Parent owns exact candidate preflight, sealed upload, and hosted terminal score.'}
    (art/'complement-integration-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
