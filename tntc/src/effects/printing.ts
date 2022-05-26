import { Effect, Variables } from './base'

export function effectToString (e: Effect): string {
  switch (e.kind) {
    case 'var': return e.name
    case 'effect': {
      const output = []
      if (e.read.kind !== 'state' || e.read.vars.length > 0) {
        output.push(`Read[${variablesToString(e.read)}]`)
      }
      if (e.update.kind !== 'state' || e.update.vars.length > 0) {
        output.push(`Update[${variablesToString(e.update)}]`)
      }
      if (output.length > 0) {
        return output.join(' & ')
      } else {
        return 'Pure'
      }
    }
    case 'arrow': return e.effects.map(effectToString).join(' -> ')
  }
}

export function variablesToString (v: Variables): string {
  switch (v.kind) {
    case 'state': return v.vars.map(v => `'${v}'`).join(', ')
    case 'quantification': return v.name
    case 'union': return v.variables.map(variablesToString).join(', ')
  }
}
