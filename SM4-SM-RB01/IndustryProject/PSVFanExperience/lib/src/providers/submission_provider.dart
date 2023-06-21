import 'package:flutter/cupertino.dart';

import 'package:psv_fan_experience/src/models/submission.dart';
import 'package:psv_fan_experience/src/models/comment.dart';

class SubmissionProvider extends ChangeNotifier {
  List<Submission> submissions = [
    Submission(
      picture: "assets/images/de96a3c94b30a52da7661daffc08-1-bg.png",
      isFromAsset: true,
      caption: "Placeholder submission",
      username: "Xavinaldo",
      competition: "BEST STADIUM SELFIE",
      comments: [
        Comment(username: "Test User 1", body: "So beautiful!"),
        Comment(username: "Test User 2", body: "So beautiful!"),
        Comment(username: "Test User 3", body: "So beautiful!"),
        Comment(username: "Test User 4", body: "So beautiful!"),
        Comment(username: "Test User 5", body: "So beautiful!"),
        Comment(username: "Test User 6", body: "So beautiful!"),
        Comment(username: "Test User 7", body: "So beautiful!"),
        Comment(username: "Test User 8", body: "So beautiful!"),
      ]
    ),
    Submission(
      picture: "assets/images/de96a3c94b30a52da7661daffc08-1-bg.png",
      isFromAsset: true,
      caption: "Placeholder submission",
      username: "Xavinaldo",
      competition: "BEST STADIUM SELFIE"
    ),
    Submission(
      picture: "assets/images/de96a3c94b30a52da7661daffc08-1-bg.png",
      isFromAsset: true,
      caption: "Placeholder submission",
      username: "Xavinaldo",
      competition: "BEST JERSEY PORTRAIT"
    ),
    Submission(
      picture: "assets/images/de96a3c94b30a52da7661daffc08-1-bg.png",
      isFromAsset: true,
      caption: "Placeholder submission",
      username: "Xavinaldo",
      competition: "BEST JERSEY PORTRAIT"
    ),
    Submission(
      picture: "assets/images/de96a3c94b30a52da7661daffc08-1-bg.png",
      isFromAsset: true,
      caption: "Placeholder submission",
      username: "Xavinaldo",
      competition: "BEST OMG MOMENTS"
    ),
    Submission(
      picture: "assets/images/de96a3c94b30a52da7661daffc08-1-bg.png",
      isFromAsset: true,
      caption: "Placeholder submission",
      username: "Xavinaldo",
      competition: "BEST OMG MOMENTS"
    ),
    Submission(
      picture: "assets/images/de96a3c94b30a52da7661daffc08-1-bg.png",
      isFromAsset: true,
      caption: "Placeholder submission",
      username: "Xavinaldo",
      competition: "BEST CLOSE UP SHOT"
    )
  ];

  createSubmission(Submission newSubmission) {
    submissions.insert(0, newSubmission);
    notifyListeners();
  }

  likeSubmission(Submission submission) {
    int index = submissions.indexOf(submission);
    submissions[index].likes += 1;
    submissions[index].isLikedByUser = !submissions[index].isLikedByUser;
    notifyListeners();
  }

  unlikeSubmission(Submission submission) {
    int index = submissions.indexOf(submission);
    submissions[index].likes -= 1;
    submissions[index].isLikedByUser = !submissions[index].isLikedByUser;
    notifyListeners();
  }

  addCommentToSubmission(Submission submission, Comment comment) {
    Submission toComment = getSubmission(submission);
    toComment.comments.insert(0, comment);
    notifyListeners();
  }

  likeComment(Submission submission, int index) {
    Submission toModify = getSubmission(submission);
    toModify.comments[index].isLikeByUser = !toModify.comments[index].isLikeByUser;
    notifyListeners();
  }

  getSubmission(Submission submission) => submissions[submissions.indexOf(submission)];
}