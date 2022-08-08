package gui;

import java.net.URL;
import java.util.ResourceBundle;

import javafx.fxml.FXML;
import javafx.fxml.Initializable;
import javafx.scene.control.Label;
import javafx.scene.control.TextArea;
import polls.Poll;
import polls.PollCategorico;
import polls.PollOrdinale;
import polls.PollReferendum;
import system.SystemEvote;

public class PollDescriptionController implements Initializable {

    @FXML
    private Label label_dataFine;

    @FXML
    private Label label_dataInizio;

    @FXML
    private Label label_nome;

    @FXML
    private Label label_tipo;

    @FXML
    private TextArea msg_field;

	@Override
	public void initialize(URL location, ResourceBundle resources) {
		// TODO Auto-generated method stub
		Poll p = SystemEvote.getInstance().getSession().getPoll();
		label_nome.setText(p.getName());
		label_dataInizio.setText(p.getStartDate().toString());
		label_dataFine.setText(p.getEndDate().toString());
		String str = "";
		if(p instanceof PollReferendum) {
			label_tipo.setText("Referendum");
			str += "Quorum: " + ((PollReferendum)p).getQuorum();
		} else if(p instanceof PollOrdinale) {
			label_tipo.setText("Votazione ordinale");
			str += "Maggioranza assoluta: " + ((PollOrdinale)p).getAbsoluteMajority();
		} else if(p instanceof PollCategorico) {
			label_tipo.setText("Votazione categorica");
			str += "Maggioranza assoluta: " + ((PollCategorico)p).getAbsoluteMajority();
			str += "\nCon preferenze: " + ((PollCategorico)p).getWithPreferences();
		} else {
			throw new IllegalArgumentException("Tipo di votazione non supportato.");
		}
		str += "\n" + p.getDescription();
		msg_field.setText(str);
	}

}
