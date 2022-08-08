package gui;

import java.io.IOException;
import java.net.URL;
import java.util.List;
import java.util.Objects;
import java.util.ResourceBundle;

import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.fxml.Initializable;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.text.Font;
import javafx.scene.text.FontPosture;
import javafx.scene.text.Text;
import javafx.scene.text.TextFlow;
import javafx.stage.Stage;
import politics.PoliticalEntity;
import polls.Poll;
import system.SystemEvote;
import polls.Vote;

public class ElectorVoteReviewController implements Initializable {
	
	private final Poll p;
	private final List<PoliticalEntity> vote;
	
    @FXML
    private Button cancelButton;

    @FXML
    private Button confirmButton;

    @FXML
    private Label pollLabel;

    @FXML
    private TextFlow textFlow;

    @FXML
    void handleCancelButton(ActionEvent event) {
    	cancelButton.getScene().getWindow().hide();
    	showVoteInterface(p);
    }

    @FXML
    void handleConfirmButton(ActionEvent event) {
    	sendVote();
    	confirmButton.getScene().getWindow().hide();
    }
    
    public ElectorVoteReviewController(Poll p, List<PoliticalEntity> vote) {
    	this.p = Objects.requireNonNull(p);
    	this.vote = Objects.requireNonNull(vote);
    }
    
	@Override
	public void initialize(URL location, ResourceBundle resources) {
		
		pollLabel.setText(p.getName());	
		
		String str = "Hai selezionato:";
		if(vote.size() == 0) {
			str += "\nSCHEDA BIANCA";
		}
		for(int i=0 ; i < vote.size() ; i++) {
			PoliticalEntity e = vote.get(i);
			str += "\n" + (i+1) + ": " + e.toString();
		}
		str += "\n\n\nDesideri confermare la tua scelta?";
		
		Text msg = new Text(str);
		msg.setFont(Font.font("Helvetica", FontPosture.ITALIC, 18));
		textFlow.getChildren().add(msg);
	}
	
	private void sendVote() {
		try {
			Vote v = p.vote(vote);
			SystemEvote.getInstance().sendVote(p, v);
		} catch(Exception e) {
			showErrorMessage(e.getMessage());
		}
	}
	
	private void showVoteInterface(Poll poll) {
		Objects.requireNonNull(poll);
		try {
    		FXMLLoader loader = new FXMLLoader(getClass().getResource("ElectorVoteEditor.fxml"));
    		ElectorVoteEditorController controller = new ElectorVoteEditorController(poll);
    		loader.setController(controller);
    		Parent root = loader.load();
            Stage stage = new Stage();
        	stage.setTitle("Scheda elettorale");
        	stage.setScene(new Scene(root, 900, 700));
        	stage.setResizable(false);
        	stage.show();
		}catch (IOException e) {
			showErrorMessage(e.getMessage());
		}
	}
	
	private void showErrorMessage(String s) {
		Objects.requireNonNull(s);
		String msg = "ERROR:\n\n";
		msg += s;
		try {
			FXMLLoader loader = new FXMLLoader(getClass().getResource("GeneralMessage.fxml"));
    		GeneralMessageController controller = new GeneralMessageController(msg);
    		loader.setController(controller);
    		Parent root = loader.load();
            Stage stage = new Stage();
        	stage.setTitle("ERROR");
        	stage.setScene(new Scene(root, 600, 400));
        	stage.setResizable(false);
        	stage.show();
		} catch (Exception e) {
			showErrorMessage(e.getMessage());
			e.printStackTrace();
		}
	}

}
