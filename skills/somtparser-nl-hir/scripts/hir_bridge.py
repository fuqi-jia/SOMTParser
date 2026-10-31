"""Agent bridge for direct SMT-LIB proposals and optional HIR construction."""
from pathlib import Path
import argparse
import json
import sys


def read_json(path):
    return json.loads(Path(path).read_text(encoding='utf-8'))


def write_json(path, value):
    Path(path).write_text(json.dumps(value, ensure_ascii=False, indent=2,
                                    allow_nan=False) + '\n', encoding='utf-8')


def main(argv=None):
    from somtparser.hir import hir_api
    from somtparser.natural_language import Candidate, compile_candidate, propose_nl

    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='command', required=True)
    request = commands.add_parser('request')
    validate = commands.add_parser('validate')
    for command in (request, validate):
        command.add_argument('source', type=Path)
        command.add_argument('--language', choices=('smtlib2', 'hir'), default='hir',
                             help='Proposal format; hir remains the legacy CLI default')
        command.add_argument('--context', type=Path)
        command.add_argument('--required-outputs', type=Path)
    validate.add_argument('model', type=Path)
    validate.add_argument('--out', type=Path, required=True)
    compile_parser = commands.add_parser('compile')
    compile_parser.add_argument('candidate', type=Path)
    compile_parser.add_argument('--digest', required=True)
    compile_parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args(argv)

    if args.command != 'compile' and args.required_outputs and args.language != 'hir':
        parser.error('--required-outputs currently requires --language hir')

    if args.command == 'compile':
        candidate = Candidate.from_json(args.candidate.read_text(encoding='utf-8'))
        result = compile_candidate(candidate, accept_digest=args.digest)
        args.out.mkdir(parents=True, exist_ok=False)
        write_json(args.out / 'report.json', result.report())
        if not result.ok:
            print(json.dumps({'ok': False, 'diagnostics': list(result.diagnostics)}))
            return 2
        (args.out / 'model.smt2').write_text(result.to_smt2(), encoding='utf-8')
        print(json.dumps({'ok': True, 'candidate_digest': candidate.digest,
                          'output': str(args.out / 'model.smt2')}))
        return 0

    source = args.source.read_text(encoding='utf-8')
    options = dict(language=args.language, context=read_json(args.context) if args.context else {})
    if args.required_outputs:
        options['required_outputs'] = read_json(args.required_outputs)
    if args.command == 'request':
        # Let the public entrypoint construct its exact current request. Stop
        # at the provider boundary; do not construct a fake HIR candidate.
        class RequestCaptured(Exception):
            pass

        captured = {}

        def capture(request):
            captured.update(request)
            raise RequestCaptured()

        try:
            propose_nl(source, provider=capture, **options)
        except RequestCaptured:
            pass
        if args.language == 'hir':
            captured['operator_catalog'] = hir_api()
        print(json.dumps(captured, ensure_ascii=False, indent=2, allow_nan=False))
        return 0

    model = read_json(args.model)

    def agent_model(request):
        return model

    candidate = propose_nl(source, provider=agent_model, **options)
    args.out.mkdir(parents=True, exist_ok=False)
    (args.out / 'candidate.json').write_text(candidate.to_json() + '\n', encoding='utf-8')
    report = dict(valid=candidate.valid, digest=candidate.digest,
                  language_configuration=args.language,
                  source_sha256=candidate.source_sha256,
                  diagnostics=list(candidate.diagnostics),
                  diagnostic_details=candidate.diagnostic_details,
                  normalization_ledger=candidate.normalization_ledger,
                  intent_preservation='not-proved')
    write_json(args.out / 'validation.json', report)
    print(json.dumps(report, ensure_ascii=False, indent=2, allow_nan=False))
    return 0 if candidate.valid else 2


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (OSError, ValueError, TypeError, KeyError) as error:
        print(json.dumps({'ok': False, 'error': str(error)}, ensure_ascii=False), file=sys.stderr)
        raise SystemExit(2)
