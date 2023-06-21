import 'package:flutter/material.dart';
import 'package:provider/provider.dart';
import 'package:psv_fan_experience/src/models/comment.dart';
import 'package:psv_fan_experience/src/models/user.dart';

import 'package:psv_fan_experience/src/providers/submission_provider.dart';
import 'package:psv_fan_experience/src/models/submission.dart';

class CommentModal extends StatelessWidget {
  CommentModal({super.key, required this.submission});

  final Submission submission;
  final TextEditingController controller = TextEditingController();

  void createComment(BuildContext context, SubmissionProvider provider) {
    Comment newComment = Comment(
        username: User.placeholderUser.username,
        body: controller.text
    );

    provider.addCommentToSubmission(submission, newComment);
    ScaffoldMessenger.of(context).showSnackBar(
      const SnackBar(content: Text("Your comment has been sent!"))
    );
    controller.text = "";
  }

  @override
  Widget build(BuildContext context) {
    return Consumer<SubmissionProvider>(
      builder: (context, provider, _) => Container(
        decoration: const BoxDecoration(
          borderRadius: BorderRadius.only(
            topLeft: Radius.circular(10.0),
            topRight: Radius.circular(10.0),
          ),
        ),
        height: MediaQuery.of(context).size.height * .5,
        child: SingleChildScrollView(
          child: Column(
            children: [
              ListTile(
                title: const Text(
                  "Comments",
                  textAlign: TextAlign.center,
                  style: TextStyle(color: Colors.black)
                ),
                shape: const RoundedRectangleBorder(
                  borderRadius: BorderRadius.only(
                    topLeft: Radius.circular(10.0),
                    topRight: Radius.circular(10.0),
                  ),
                ),
                tileColor: Theme.of(context).colorScheme.tertiary,
              ),
              SizedBox(
                height: MediaQuery.of(context).size.height * .335,
                child: provider.getSubmission(submission).comments.isNotEmpty ? ListView.separated(
                  itemBuilder: (context, index) => ListTile(
                    leading: CircleAvatar(
                      child: Image.asset('assets/images/usericon.png'),
                    ),
                    title: Text(
                      provider.getSubmission(submission).comments[index].username,
                      style: const TextStyle(color: Colors.black)
                    ),
                    subtitle: Text(
                      provider.getSubmission(submission).comments[index].body,
                      style: const TextStyle(color: Colors.black)
                    ),
                    trailing: IconButton(
                      icon: provider.getSubmission(submission).comments[index].isLikeByUser
                        ? Icon(Icons.favorite, color: Theme.of(context).colorScheme.primary)
                        : Icon(Icons.favorite_outline, color: Theme.of(context).colorScheme.tertiary),
                      onPressed: () {
                        provider.likeComment(submission, index);
                      }
                    ),
                  ),
                  separatorBuilder: (context, index) => const Divider(),
                  itemCount: provider.getSubmission(submission).comments.length
                ) : const Center(
                  child: Text(
                    "Submission doesn't have comments for now.",
                    textAlign: TextAlign.center,
                    style: TextStyle(color: Colors.black)
                  )
                ),
              ),
              ListTile(
                titleAlignment: ListTileTitleAlignment.center,
                title: TextField(
                  controller: controller,
                  textInputAction: TextInputAction.done,
                  onSubmitted: (_) => createComment(context, provider),
                  decoration: InputDecoration(
                    suffixIcon: IconButton(
                      icon: const Icon(Icons.send),
                      color: Theme.of(context).colorScheme.primary,
                      onPressed: () => createComment(context, provider)
                    ),
                    filled: true,
                    fillColor: Theme.of(context).colorScheme.background,
                    border: const OutlineInputBorder(
                      borderRadius: BorderRadius.all(Radius.circular(8.0))
                    ),
                  ),
                ),
                tileColor: Theme.of(context).colorScheme.tertiary,
              ),
            ],
          ),
        ),
      ),
    );
  }
}