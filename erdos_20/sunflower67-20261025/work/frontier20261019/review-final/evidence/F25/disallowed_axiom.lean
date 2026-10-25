import FrontierAudit
namespace IsolatedNegativeControl
axiom intentionallyUntrusted : False
theorem forbiddenRoot : False := intentionallyUntrusted
end IsolatedNegativeControl
#frontier_audit IsolatedNegativeControl.forbiddenRoot
